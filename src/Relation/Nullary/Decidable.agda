------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on and properties of decidable relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Decidable where

open import Level using (Level)
open import Data.Bool.Base using (true; false)
open import Data.Product.Base as Prod hiding (map)
open import Data.Sum.Base as Sum hiding (map)
open import Function.Base
open import Function.Bundles using
  (Injection; module Injection; module Equivalence; _⇔_; _↔_; mk↔′)
open import Relation.Binary.Bundles using (Setoid; module Setoid)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (Irrelevant)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong′)

private
  variable
    p q r : Level
    P Q R : Set p

------------------------------------------------------------------------
-- Re-exporting the core definitions

open import Relation.Nullary.Decidable.Core public

------------------------------------------------------------------------
-- Maps

map : P ⇔ Q → Dec P → Dec Q
map P⇔Q = map′ to from
  where open Equivalence P⇔Q

module _ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
         (inj : Injection A B)
  where

  open Injection inj
  open Setoid A using () renaming (_≈_ to _≈A_)
  open Setoid B using () renaming (_≈_ to _≈B_)

  -- If there is an injection from one setoid to another, and the
  -- latter's equivalence relation is decidable, then the former's
  -- equivalence relation is also decidable.

  via-injection : Decidable _≈B_ → Decidable _≈A_
  via-injection dec x y =
    map′ injective cong (dec (to x) (to y))

------------------------------------------------------------------------
-- A lemma relating True and Dec

True-↔ : (dec : Dec P) → Irrelevant P → True dec ↔ P
True-↔ (true  because [p]) irr = let p = invert [p] in
  mk↔′ (λ _ → p) _ (irr p) cong′
True-↔ (false because [¬p]) _  = let ¬p = invert [¬p] in
  mk↔′ (λ ()) ¬p (λ p → contradiction p ¬p) λ ()

------------------------------------------------------------------------
-- Result of decidability

isYes≗does : (P? : Dec P) → isYes P? ≡ does P?
isYes≗does (true  because _) = refl
isYes≗does (false because _) = refl

dec-true : (p? : Dec P) → P → does p? ≡ true
dec-true (true  because   _ ) p = refl
dec-true (false because [¬p]) p = contradiction p (invert [¬p])

dec-false : (p? : Dec P) → ¬ P → does p? ≡ false
dec-false (false because  _ ) ¬p = refl
dec-false (true  because [p]) ¬p = contradiction (invert [p]) ¬p

dec-yes : (p? : Dec P) → P → ∃ λ p′ → p? ≡ yes p′
dec-yes p? p with dec-true p? p
dec-yes (yes p′) p | refl = p′ , refl

dec-no : (p? : Dec P) (¬p : ¬ P) → p? ≡ no ¬p
dec-no p? ¬p with dec-false p? ¬p
dec-no (no _) _ | refl = refl

dec-yes-irr : (p? : Dec P) → Irrelevant P → (p : P) → p? ≡ yes p
dec-yes-irr p? irr p with p′ , eq ← dec-yes p? p rewrite irr p p′ = eq
