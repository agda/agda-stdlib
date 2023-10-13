------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on and properties of decidable relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Decidable where

open import Level using (Level)
open import Data.Bool.Base using (true; false)
open import Data.Product.Base using (∃; _,_)
open import Function.Base
open import Function.Bundles using
  (Injection; module Injection; module Equivalence; _⇔_; _↔_; mk↔ₛ′)
open import Relation.Binary.Bundles using (Setoid; module Setoid)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (invert; ¬_; contradiction; Irrelevant)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong′)

private
  variable
    a b ℓ₁ ℓ₂ : Level
    A B : Set a

------------------------------------------------------------------------
-- Re-exporting the core definitions

open import Relation.Nullary.Decidable.Core public

------------------------------------------------------------------------
-- Maps

map : A ⇔ B → Dec A → Dec B
map A⇔B = map′ to from
  where open Equivalence A⇔B

-- If there is an injection from one setoid to another, and the
-- latter's equivalence relation is decidable, then the former's
-- equivalence relation is also decidable.
via-injection : {S : Setoid a ℓ₁} {T : Setoid b ℓ₂}
                (inj : Injection S T) (open Injection inj) →
                Decidable Eq₂._≈_ → Decidable Eq₁._≈_
via-injection inj _≟_ x y = map′ injective cong (to x ≟ to y)
  where open Injection inj

------------------------------------------------------------------------
-- A lemma relating True and Dec

True-↔ : (a? : Dec A) → Irrelevant A → True a? ↔ A
True-↔ (yes′ [a]) irr = let  a = invert  [a] in mk↔ₛ′ (λ _ → a) _ (irr a) cong′
True-↔ (no′ [¬a]) _   = let ¬a = invert [¬a] in mk↔ₛ′ (λ ()) ¬a (λ a → contradiction a ¬a) λ ()

------------------------------------------------------------------------
-- Result of decidability

isYes≗does : (a? : Dec A) → isYes a? ≡ does a?
isYes≗does (yes′ _) = refl
isYes≗does (no′  _) = refl

dec-true : (a? : Dec A) → A → does a? ≡ true
dec-true (yes′  _ ) a = refl
dec-true (no′ [¬a]) a = contradiction a (invert [¬a])

dec-false : (a? : Dec A) → ¬ A → does a? ≡ false
dec-false (no′   _ ) ¬a = refl
dec-false (yes′ [a]) ¬a = contradiction (invert [a]) ¬a

dec-yes : (a? : Dec A) → A → ∃ λ a → a? ≡ yes a
dec-yes a? a with dec-true a? a
dec-yes (yes a′) a | refl = a′ , refl

dec-no : (a? : Dec A) (¬a : ¬ A) → a? ≡ no ¬a
dec-no a? ¬a with dec-false a? ¬a
dec-no (no _) _ | refl = refl

dec-yes-irr : (a? : Dec A) → Irrelevant A → (a : A) → a? ≡ yes a
dec-yes-irr a? irr a with dec-yes a? a
... | a′ , eq rewrite irr a a′ = eq
