------------------------------------------------------------------------
-- The Agda standard library
--
-- Example use of the 'PunchIn' view of Fin
--
-- This is an example of a view of a function defined over a datatype,
-- such that the recursion and call-pattern(s) of the function are
-- precisely mirrored in the constructors of the view type
--
-- Using this view, we can exhibit the corresponding properties of
-- the function `punchIn` defined in `Data.Fin.Properties`
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Data.Fin.Relation.Ternary.PunchIn where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; zero; suc; _≤_; punchIn)
open import Data.Fin.Relation.Ternary.PunchIn
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Properties of the function, derived from properties of the View

punchInᵢ≢i : ∀ i (j : Fin n) → punchIn i j ≢ i
punchInᵢ≢i i j = view-codomain (view i j)

punchIn-injective : ∀ i (j k : Fin n) →
                    punchIn i j ≡ punchIn i k → j ≡ k
punchIn-injective i j k = view-injective (view i j) (view i k)

punchIn-mono≤ : ∀ (i : Fin (suc n)) {j k} →
                j ≤ k → punchIn i j ≤ punchIn i k
punchIn-mono≤ i {j} {k} = view-mono-≤ (view i j) (view i k)

punchIn-cancel≤ : ∀ (i : Fin (suc n)) {j k} →
                  (punchIn i j ≤ punchIn i k) → j ≤ k
punchIn-cancel≤ i {j} {k} = view-cancel-≤ (view i j) (view i k)

