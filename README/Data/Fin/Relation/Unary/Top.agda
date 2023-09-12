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
-- together with their corresponding properties in `Data.Fin.Properties`:
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module README.Data.Fin.Relation.Unary.Top where

open import Data.Nat.Base using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Nat.Properties using (n∸n≡0; +-∸-assoc; ≤-reflexive)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; inject₁; _>_)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ<n; toℕ-inject₁)
open import Data.Fin.Induction hiding (>-weakInduction)
open import Data.Fin.Relation.Unary.Top
open import Data.Fin.Relation.Unary.Top.Instances
open import Induction.WellFounded as WF
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (Pred)

private
  variable
    ℓ : Level
    n : ℕ
    i : Fin (suc n)
    j : Fin n

------------------------------------------------------------------------
-- Inverting inject₁

-- The principal purpose of this View of Fin (suc n) is that it provides
-- a *partial inverse* to the function inject₁, as follows:
--
-- * pattern matching of the form `... inj j ← view {n} i` ensures that
--   `i ≟ inject₁ j`, and hence that `j` is, *definitionally*, an image
--   under a hypothetical inverse to `inject₁`;
--
-- * such patterns are irrefutable *precisely* when `i` is in the codomain
--   of `inject₁`, which by property `fromℕ≢inject₁`, is equivalent to the
--   condition `i ≢ fromℕ n`, or again equivalently, `toℕ i ≢ n`, each
--   equivalent to `IsInject₁ {n} (view i)`, hence amenable to instance resolution
--
-- Definition
--
-- Rather than redefine `lower₁` of `Data.Fin.Base`, we instead define

inject₁⁻¹ : (i : Fin (suc n)) → .{{IsInject₁ (view i)}} → Fin n
inject₁⁻¹ i with ‵inject₁ j ← view i = j

-- Properties, by analogy with those for `lower₁` in `Data.Fin.Properties`

inject₁⁻¹-irrelevant : (i : Fin (suc n)) .{{ii₁ ii₂ : IsInject₁ (view i)}} →
                       inject₁⁻¹ i {{ii₁}} ≡ inject₁⁻¹ i {{ii₂}}
inject₁⁻¹-irrelevant i with ‵inj₁ _ ← view i = refl

inject₁-inject₁⁻¹ : (i : Fin (suc n)) .{{_ : IsInject₁ (view i)}} →
                    inject₁ (inject₁⁻¹ i) ≡ i
inject₁-inject₁⁻¹ i with ‵inj₁ _ ← view i = refl

inject₁⁻¹-inject₁ : (j : Fin n) → inject₁⁻¹ (inject₁ j) ≡ j
inject₁⁻¹-inject₁ j rewrite view-inject₁ j = refl

inject₁≡⇒inject₁⁻¹≡ : (eq : inject₁ {n} j ≡ i) →
                      let instance _ = inject₁≡⁺ eq in inject₁⁻¹ i ≡ j
inject₁≡⇒inject₁⁻¹≡ refl = inject₁⁻¹-inject₁ _

inject₁⁻¹-injective : (i₁ i₂ : Fin (suc n)) →
                      .{{_ : IsInject₁ (view i₁)}} →
                      .{{_ : IsInject₁ (view i₂)}} →
                      inject₁⁻¹ i₁ ≡ inject₁⁻¹ i₂ → i₁ ≡ i₂
inject₁⁻¹-injective i₁ i₂ with ‵inj₁ _ ← view i₁ | ‵inj₁ _ ← view i₂ = cong inject₁

toℕ-inject₁⁻¹ : (i : Fin (suc n)) → .{{_ : IsInject₁ (view i)}} →
                toℕ (inject₁⁻¹ i) ≡ toℕ i
toℕ-inject₁⁻¹ i with ‵inject₁ j ← view i = sym (toℕ-inject₁ j)

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
        | view-fromℕ n             = refl
opposite-involutive {suc n} (suc i)
  rewrite opposite-suc≡inject₁-opposite i
        | view-inject₁(opposite i) = cong suc (opposite-involutive i)

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
  suc (n ∸ suc (toℕ j))  ≡˘⟨ +-∸-assoc 1 {n} {suc (toℕ j)} (toℕ<n j) ⟩
  n ∸ toℕ j              ≡˘⟨ cong (n ∸_) (toℕ-inject₁ j) ⟩
  n ∸ toℕ (inject₁ j)    ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- Reimplementation of `Data.Fin.Induction.>-weakInduction`

open WF using (Acc; acc)

>-weakInduction : (P : Pred (Fin (suc n)) ℓ) →
                  P (fromℕ n) →
                  (∀ i → P (suc i) → P (inject₁ i)) →
                  ∀ i → P i
>-weakInduction {n = n} P Pₙ Pᵢ₊₁⇒Pᵢ i = induct (>-wellFounded i)
  where
  induct : ∀ {i} → Acc _>_ i → P i
  induct {i} (acc rec) with view i
  ... | ‵fromℕ = Pₙ
  ... | ‵inject₁ j = Pᵢ₊₁⇒Pᵢ j (induct (rec _ inject₁[j]+1≤[j+1]))
    where
    inject₁[j]+1≤[j+1] : suc (toℕ (inject₁ j)) ≤ toℕ (suc j)
    inject₁[j]+1≤[j+1] = ≤-reflexive (toℕ-inject₁ (suc j))
