------------------------------------------------------------------------
-- The Agda standard library
--
-- Example use of the 'PunchOut' view of Fin
--
-- This is an example of a view of a function defined over a datatype,
-- such that the recursion and call-pattern(s) of the function are
-- precisely mirrored in the constructors of the view type
--
-- Using this view, we can exhibit the corresponding properties of
-- the function `punchOut` defined in `Data.Fin.Properties`
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Data.Fin.Relation.Ternary.PunchOut where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; zero; suc; _≤_; punchIn; punchOut)
open import Data.Fin.Properties using (punchInᵢ≢i)
open import Data.Fin.Relation.Ternary.PunchIn as PunchIn using ()
open import Data.Fin.Relation.Ternary.PunchOut
open import Function.Base using (_∘_)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Properties of the function, derived from properties of the View

punchOut-injective : ∀ {i j k : Fin (suc n)} (i≢j : i ≢ j) (i≢k : i ≢ k) →
                    punchOut i≢j ≡ punchOut i≢k → j ≡ k
punchOut-injective i≢j i≢k = view-injective (view i≢j) (view i≢k)

punchOut-cong : ∀ (i : Fin (suc n)) {j k} {i≢j : i ≢ j} {i≢k : i ≢ k} →
                j ≡ k → punchOut i≢j ≡ punchOut i≢k
punchOut-cong i {i≢j = i≢j} {i≢k = i≢k} = view-cong (view i≢j) (view i≢k)

punchOut-mono-≤ : ∀ {i j k : Fin (suc n)} (i≢j : i ≢ j) (i≢k : i ≢ k) →
                j ≤ k → punchOut i≢j ≤ punchOut i≢k
punchOut-mono-≤ i≢j i≢k = view-mono-≤ (view i≢j) (view i≢k)

punchOut-cancel-≤ : ∀ {i j k : Fin (suc n)} (i≢j : i ≢ j) (i≢k : i ≢ k) →
                  (punchOut i≢j ≤ punchOut i≢k) → j ≤ k
punchOut-cancel-≤ i≢j i≢k = view-cancel-≤ (view i≢j) (view i≢k)

-- punchOut and punchIn are mutual inverses,
-- because their corresponding View s are converses

punchIn-punchOut : ∀ {i j : Fin (suc n)} (i≢j : i ≢ j) →
                   punchIn i (punchOut i≢j) ≡ j
punchIn-punchOut = PunchIn.view-complete ∘ view-view⁻¹ ∘ view

punchOut-punchIn : ∀ i {j : Fin n} →
                   punchOut {i = i} {j = punchIn i j} (punchInᵢ≢i i j ∘ sym) ≡ j
punchOut-punchIn i {j} = view-complete (view⁻¹-view (PunchIn.view i j))
