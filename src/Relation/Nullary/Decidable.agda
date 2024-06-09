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
open import Function.Bundles using
  (Injection; module Injection; module Equivalence; _⇔_; _↔_; mk↔ₛ′)
open import Relation.Binary.Bundles using (Setoid; module Setoid)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (Irrelevant)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong′)

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
True-↔ (true  because [a]) irr = let a = invert [a] in mk↔ₛ′ (λ _ → a) _ (irr a) cong′
True-↔ (false because [¬a]) _  = let ¬a = invert [¬a] in mk↔ₛ′ (λ ()) ¬a (λ a → contradiction a ¬a) λ ()

------------------------------------------------------------------------
-- Result of decidability

isYes≗does : (a? : Dec A) → isYes a? ≡ does a?
isYes≗does (true  because _) = refl
isYes≗does (false because _) = refl

dec-true : (a? : Dec A) → A → does a? ≡ true
dec-true (true  because   _ ) a = refl
dec-true (false because [¬a]) a = contradiction a (invert [¬a])

dec-false : (a? : Dec A) → ¬ A → does a? ≡ false
dec-false (false because  _ ) ¬a = refl
dec-false (true  because [a]) ¬a = contradiction (invert [a]) ¬a

dec-yes : (a? : Dec A) → A → ∃ λ a → a? ≡ yes a
dec-yes a? a with yes a′ ← a? | refl ← dec-true a? a = a′ , refl

dec-no : (a? : Dec A) (¬a : ¬ A) → a? ≡ no ¬a
dec-no a? ¬a with no _ ← a? | refl ← dec-false a? ¬a = refl

dec-yes-irr : (a? : Dec A) → Irrelevant A → (a : A) → a? ≡ yes a
dec-yes-irr a? irr a with a′ , eq ← dec-yes a? a rewrite irr a a′ = eq

⌊⌋-map′ : ∀ t f (a? : Dec A) → ⌊ map′ {B = B} t f a? ⌋ ≡ ⌊ a? ⌋
⌊⌋-map′ t f a? = trans (isYes≗does (map′ t f a?)) (sym (isYes≗does a?))
