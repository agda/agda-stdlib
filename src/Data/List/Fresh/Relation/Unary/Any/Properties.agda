------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Any predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Fresh.Relation.Unary.Any.Properties where

open import Data.Bool.Base using (true; false)
open import Data.List.Fresh using (List#; _∷#_; _#_; NonEmpty; cons; length; [])
open import Data.List.Fresh.Relation.Unary.All using (All; _∷_; append; [])
open import Data.List.Fresh.Relation.Unary.Any using (Any; here; there; _─_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘′_)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
open import Relation.Nary using (∀[_]; _⇒_; ∁; Decidable)
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Unary as Unary using (Pred)

private
  variable
    a b p q r s : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred A q
    R : Rel A r
    xs ys : List# A R


------------------------------------------------------------------------
-- NonEmpty

Any⇒NonEmpty : Any P xs → NonEmpty xs
Any⇒NonEmpty {xs = cons x xs pr} p  = cons x xs pr

------------------------------------------------------------------------
-- Correspondence between Any and All

module _ (P⇒¬Q : ∀[ P ⇒ ∁ Q ]) where

  Any⇒¬All : Any P xs → ¬ (All Q xs)
  Any⇒¬All (here p)   (q ∷ _)  = P⇒¬Q p q
  Any⇒¬All (there ps) (_ ∷ qs) = Any⇒¬All ps qs

  All⇒¬Any : All P xs → ¬ (Any Q xs)
  All⇒¬Any (p ∷ _)  (here q)   = P⇒¬Q p q
  All⇒¬Any (_ ∷ ps) (there qs) = All⇒¬Any ps qs

module _ (P? : Decidable P) where

  ¬All⇒Any : ¬ (All P xs) → Any (∁ P) xs
  ¬All⇒Any {xs = []}      ¬ps = contradiction [] ¬ps
  ¬All⇒Any {xs = x ∷# xs} ¬ps with P? x
  ... |  true because  [p] = there (¬All⇒Any (¬ps ∘′ (invert [p] ∷_)))
  ... | false because [¬p] = here (invert [¬p])

  ¬Any⇒All : ¬ (Any P xs) → All (∁ P) xs
  ¬Any⇒All {xs = []}      ¬ps = []
  ¬Any⇒All {xs = x ∷# xs} ¬ps with P? x
  ... |  true because  [p] = contradiction (here (invert [p])) ¬ps
  ... | false because [¬p] = invert [¬p] ∷ ¬Any⇒All (¬ps ∘′ there)

------------------------------------------------------------------------
-- remove

length-remove : (k : Any P xs) → length xs ≡ suc (length (xs ─ k))
length-remove (here _)  = refl
length-remove (there p) = cong suc (length-remove p)

------------------------------------------------------------------------
-- append

append⁺ˡ : {ps : All (_# ys) xs} → Any P xs → Any P (append xs ys ps)
append⁺ˡ (here px) = here px
append⁺ˡ (there p) = there (append⁺ˡ p)

append⁺ʳ : {ps : All (_# ys) xs} → Any P ys → Any P (append xs ys ps)
append⁺ʳ {xs = []}      p = p
append⁺ʳ {xs = x ∷# xs} p = there (append⁺ʳ p)

append⁻ : ∀ xs {ys} {ps : All {R = R} (_# ys) xs} →
          Any P (append xs ys ps) → Any P xs ⊎ Any P ys
append⁻ []        p         = inj₂ p
append⁻ (x ∷# xs) (here px) = inj₁ (here px)
append⁻ (x ∷# xs) (there p) = Sum.map₁ there (append⁻ xs p)
