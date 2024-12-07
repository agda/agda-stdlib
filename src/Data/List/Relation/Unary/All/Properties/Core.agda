------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.All.Properties.Core where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Bool.Base using (true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Product.Base as Product using (_,_)
open import Function.Base using (_∘_; _$_)
open import Function.Bundles using (_↠_; mk↠ₛ; _⇔_; mk⇔)
open import Level using (Level)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Decidable.Core using (_because_)
open import Relation.Unary using (Decidable; Pred; Universal)

private
  variable
    a b p ℓ : Level
    A : Set a
    B : Set b
    P : Pred A p
    x y : A
    xs ys : List A

------------------------------------------------------------------------
-- Lemmas relating Any, All and negation.

¬Any⇒All¬ : ∀ xs → ¬ Any P xs → All (¬_ ∘ P) xs
¬Any⇒All¬ []       ¬p = []
¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ here ∷ ¬Any⇒All¬ xs (¬p ∘ there)

All¬⇒¬Any : ∀ {xs} → All (¬_ ∘ P) xs → ¬ Any P xs
All¬⇒¬Any (¬p ∷ _)  (here  p) = ¬p p
All¬⇒¬Any (_  ∷ ¬p) (there p) = All¬⇒¬Any ¬p p

¬All⇒Any¬ : Decidable P → ∀ xs → ¬ All P xs → Any (¬_ ∘ P) xs
¬All⇒Any¬ dec []       ¬∀ = contradiction [] ¬∀
¬All⇒Any¬ dec (x ∷ xs) ¬∀ with dec x
... |  true because  [p] = there (¬All⇒Any¬ dec xs (¬∀ ∘ _∷_ (invert [p])))
... | false because [¬p] = here (invert [¬p])

Any¬⇒¬All : ∀ {xs} → Any (¬_ ∘ P) xs → ¬ All P xs
Any¬⇒¬All (here  ¬p) = ¬p           ∘ All.head
Any¬⇒¬All (there ¬p) = Any¬⇒¬All ¬p ∘ All.tail

¬Any↠All¬ : ∀ {xs} → (¬ Any P xs) ↠ All (¬_ ∘ P) xs
¬Any↠All¬ = mk↠ₛ {to = ¬Any⇒All¬ _} (λ y → All¬⇒¬Any y , to∘from y)
  where
  to∘from : ∀ {xs} (¬p : All (¬_ ∘ P) xs) → ¬Any⇒All¬ xs (All¬⇒¬Any ¬p) ≡ ¬p
  to∘from []         = refl
  to∘from (¬p ∷ ¬ps) = cong₂ _∷_ refl (to∘from ¬ps)

  -- If equality of functions were extensional, then the surjection
  -- could be strengthened to a bijection.

  from∘to : Extensionality _ _ →
            ∀ xs → (¬p : ¬ Any P xs) → All¬⇒¬Any (¬Any⇒All¬ xs ¬p) ≡ ¬p
  from∘to ext []       ¬p = ext λ ()
  from∘to ext (x ∷ xs) ¬p = ext λ
    { (here p)  → refl
    ; (there p) → cong (λ f → f p) $ from∘to ext xs (¬p ∘ there)
    }

Any¬⇔¬All : ∀ {xs} → Decidable P → Any (¬_ ∘ P) xs ⇔ (¬ All P xs)
Any¬⇔¬All dec = mk⇔ Any¬⇒¬All (¬All⇒Any¬ dec _)

private
  -- If equality of functions were extensional, then the logical
  -- equivalence could be strengthened to a surjection.
  to∘from : Extensionality _ _ → (dec : Decidable P) →
            (¬∀ : ¬ All P xs) → Any¬⇒¬All (¬All⇒Any¬ dec xs ¬∀) ≡ ¬∀
  to∘from ext P ¬∀ = ext λ ∀P → contradiction ∀P ¬∀

module _ {_~_ : REL A B ℓ} where

  All-swap : ∀ {xs ys} →
             All (λ x → All (x ~_) ys) xs →
             All (λ y → All (_~ y) xs) ys
  All-swap {ys = []}     _   = []
  All-swap {ys = y ∷ ys} []  = All.universal (λ _ → []) (y ∷ ys)
  All-swap {ys = y ∷ ys} ((x~y ∷ x~ys) ∷ pxs) =
    (x~y ∷ (All.map All.head pxs)) ∷
    All-swap (x~ys ∷ (All.map All.tail pxs))

