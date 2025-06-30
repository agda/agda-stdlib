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
open import Function.Bundles
  using (Injection; module Injection; module Equivalence; _⇔_; _↔_; mk↔ₛ′)
open import Relation.Binary.Bundles using (Setoid; module Setoid)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Irrelevant using (Irrelevant)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; refl; sym; trans)

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

module _ {S : Setoid a ℓ₁} {T : Setoid b ℓ₂} (injection : Injection S T) where

  open Injection injection

  via-injection : Decidable Eq₂._≈_ → Decidable Eq₁._≈_
  via-injection _≟_ x y = map′ injective cong (to x ≟ to y)

------------------------------------------------------------------------
-- A lemma relating True and Dec

True-↔ : (a? : Dec A) → Irrelevant A → True a? ↔ A
True-↔ a? irr = mk↔ₛ′ to from to-from (from-to a?)
  where
  to = toWitness {a? = a?}
  from = fromWitness {a? = a?}
  to-from : ∀ a → to (from a) ≡ a
  to-from a = irr _ a
  from-to : ∀ a? (x : True a?) → fromWitness (toWitness x) ≡ x
  from-to (yes _) _ = refl

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

dec-yes-recompute : (a? : Dec A) → .(a : A) → a? ≡ yes (recompute a? a)
dec-yes-recompute a? a with yes _ ← a? | refl ← dec-true a? (recompute a? a) = refl

dec-yes-irr : (a? : Dec A) → Irrelevant A → (a : A) → a? ≡ yes a
dec-yes-irr a? irr a =
  trans (dec-yes-recompute a? a) (≡.cong yes (recompute-irrelevant-id a? irr a))

dec-yes : (a? : Dec A) → A → ∃ λ a → a? ≡ yes a
dec-yes a? a = _ , dec-yes-recompute a? a

dec-no : (a? : Dec A) (¬a : ¬ A) → a? ≡ no ¬a
dec-no a? ¬a with no _ ← a? | refl ← dec-false a? ¬a = refl

⌊⌋-map′ : ∀ t f (a? : Dec A) → ⌊ map′ {B = B} t f a? ⌋ ≡ ⌊ a? ⌋
⌊⌋-map′ t f a? = trans (isYes≗does (map′ t f a?)) (sym (isYes≗does a?))

does-≡ : (a? b? : Dec A) → does a? ≡ does b?
does-≡ a? (yes a) = dec-true a? a
does-≡ a? (no ¬a) = dec-false a? ¬a

does-⇔ : A ⇔ B → (a? : Dec A) → (b? : Dec B) → does a? ≡ does b?
does-⇔ A⇔B a? = does-≡ (map A⇔B a?)
