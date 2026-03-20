------------------------------------------------------------------------
-- The Agda standard library
--
-- Example use of the 'top' view of Fin
--
-- This is an example of a view of (elements of) a datatype,
-- here i : Fin (suc n), which exhibits every such i as
-- * either, i = fromℕ n
-- * or, i = inject₁ j for a unique j : Fin n
--
-- Using this view, we can redefine certain operations in `Data.Fin.Base`,
-- together with their corresponding properties in `Data.Fin.Properties`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Data.Fin.Relation.Unary.Top where

open import Data.Nat.Base using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Nat.Properties using (n∸n≡0; ∸-suc; ≤-reflexive)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; inject₁; _>_)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ<n; toℕ-inject₁)
open import Data.Fin.Induction hiding (>-weakInduction)
open import Data.Fin.Relation.Unary.Top
import Induction.WellFounded as WF
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (Pred)

private
  variable
    ℓ : Level
    n : ℕ

------------------------------------------------------------------------
-- Reimplementation of `Data.Fin.Base.opposite`, and its properties

-- Definition

opposite : Fin n → Fin n
opposite {suc n} i with view i
... | ‵fromℕ     = zero
... | ‵inject₁ j = suc (opposite {n} j)

-- Properties

opposite-zero≡fromℕ : ∀ n → opposite {suc n} zero ≡ fromℕ n
opposite-zero≡fromℕ zero    = refl
opposite-zero≡fromℕ (suc n) = cong suc (opposite-zero≡fromℕ n)

opposite-fromℕ≡zero : ∀ n → opposite {suc n} (fromℕ n) ≡ zero
opposite-fromℕ≡zero n rewrite view-fromℕ n = refl

opposite-suc≡inject₁-opposite : (j : Fin n) →
                                opposite (suc j) ≡ inject₁ (opposite j)
opposite-suc≡inject₁-opposite {suc n} i with view i
... | ‵fromℕ     = refl
... | ‵inject₁ j = cong suc (opposite-suc≡inject₁-opposite {n} j)

opposite-involutive : (j : Fin n) → opposite (opposite j) ≡ j
opposite-involutive {suc n} zero
  rewrite opposite-zero≡fromℕ n
        | view-fromℕ n              = refl
opposite-involutive {suc n} (suc i)
  rewrite opposite-suc≡inject₁-opposite i
        | view-inject₁ (opposite i) = cong suc (opposite-involutive i)

opposite-suc : (j : Fin n) → toℕ (opposite (suc j)) ≡ toℕ (opposite j)
opposite-suc j = begin
  toℕ (opposite (suc j))      ≡⟨ cong toℕ (opposite-suc≡inject₁-opposite j) ⟩
  toℕ (inject₁ (opposite j))  ≡⟨ toℕ-inject₁ (opposite j) ⟩
  toℕ (opposite j)            ∎ where open ≡-Reasoning

opposite-prop : (j : Fin n) → toℕ (opposite j) ≡ n ∸ suc (toℕ j)
opposite-prop {suc n} i with view i
... | ‵fromℕ  rewrite toℕ-fromℕ n | n∸n≡0 n = refl
... | ‵inject₁ j = begin
  suc (toℕ (opposite j)) ≡⟨ cong suc (opposite-prop j) ⟩
  suc (n ∸ suc (toℕ j))  ≡⟨ ∸-suc (toℕ<n j) ⟨
  n ∸ toℕ j              ≡⟨ cong (n ∸_) (toℕ-inject₁ j) ⟨
  n ∸ toℕ (inject₁ j)    ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- Reimplementation of `Data.Fin.Induction.>-weakInduction`

open WF using (Acc; acc)

>-weakInduction : (P : Pred (Fin (suc n)) ℓ) →
                  P (fromℕ n) →
                  (∀ i → P (suc i) → P (inject₁ i)) →
                  ∀ i → P i
>-weakInduction P Pₙ Pᵢ₊₁⇒Pᵢ i = induct (>-wellFounded i)
  where
  induct : ∀ {i} → Acc _>_ i → P i
  induct {i} (acc rec) with view i
  ... | ‵fromℕ = Pₙ
  ... | ‵inject₁ j = Pᵢ₊₁⇒Pᵢ j (induct (rec inject₁[j]+1≤[j+1]))
    where
    inject₁[j]+1≤[j+1] : suc (toℕ (inject₁ j)) ≤ toℕ (suc j)
    inject₁[j]+1≤[j+1] = ≤-reflexive (toℕ-inject₁ (suc j))
