------------------------------------------------------------------------
-- The Agda standard library
--
-- Example use of the 'Pinch' view of Fin
--
-- This is an example of a view of a function defined over a datatype,
-- such that the recursion and call-pattern(s) of the function are
-- precisely mirrored in the constructors of the view type
--
-- Using this view, we can exhibit the corresponding properties of
-- the function `punchIn` defined in `Data.Fin.Properties`
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Data.Fin.Relation.Ternary.Pinch where

open import Data.Nat.Base as Nat using (ℕ; suc; ∣_-_∣)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; _≤_; _<_; pinch)
open import Data.Fin.Relation.Ternary.Pinch
open import Data.Product using (_,_; ∃)
open import Function.Definitions.Core2 using (Surjective)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Properties of the function, derived from properties of the View

pinch-surjective : ∀ (i : Fin n) → Surjective _≡_ (pinch i)
pinch-surjective i k
  with j , v ← view-surjective i k
  with refl ← view-complete v = j , refl

pinch-injective : ∀ {i : Fin n} {j k : Fin (ℕ.suc n)} →
                  suc i ≢ j → suc i ≢ k → pinch i j ≡ pinch i k → j ≡ k
pinch-injective {n = n} {i} {j} {k} = view-injective (view i j) (view i k)

pinch-mono-≤ : ∀ (i : Fin n) → (pinch i) Preserves _≤_ ⟶ _≤_
pinch-mono-≤ i {j} {k} = view-mono-≤ (view i j) (view i k)

pinch-cancel-< : ∀ (i : Fin (suc n)) {j k} →
                (pinch i j < pinch i k) → j < k
pinch-cancel-< i {j} {k} = view-cancel-< (view i j) (view i k)

pinch-≡⇒∣j-k∣≤1 : ∀ (i : Fin n) {j k} →
                  (pinch i j ≡ pinch i k) → ∣ (toℕ j) - (toℕ k) ∣ Nat.≤ 1
pinch-≡⇒∣j-k∣≤1 i {j} {k} = view-j≡view-k⇒∣j-k∣≤1 (view i j) (view i k)

