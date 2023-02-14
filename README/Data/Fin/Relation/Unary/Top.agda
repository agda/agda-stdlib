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
-- together with their corresponding properties in `Data.Fin.Properties`
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Data.Fin.Relation.Unary.Top where

open import Data.Nat.Base using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Nat.Properties using (n∸n≡0; +-∸-assoc; ≤-reflexive)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; inject₁; _>_)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ<n; toℕ-inject₁)
open import Data.Fin.Induction hiding (>-weakInduction)
open import Data.Fin.Relation.Unary.Top
open import Induction.WellFounded as WF
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (Pred)

private
  variable
    ℓ : Level
    n : ℕ

open Instances

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
--   equivalent to `IsInj {n} (view i)`, hence amenable to instance resolution
--
-- Definition
--
-- Rather than redefine `lower₁` of `Data.Fin.Base`, we instead define

inject₁⁻¹ : (i : Fin (suc n)) → .{{IsInj (view {n} i)}} → Fin n
inject₁⁻¹ i with inj j ← view i = j

-- Properties, by analogy with those for `lower₁` in `Data.Fin.Properties

inject₁⁻¹-irrelevant : (i : Fin (suc n)) .{{ii₁ ii₂ : IsInj (view {n} i)}} →
                       inject₁⁻¹ i {{ii₁}} ≡ inject₁⁻¹ i {{ii₂}}
inject₁⁻¹-irrelevant i with inj ii ← view i = refl

inject₁-inject₁⁻¹ : (i : Fin (suc n)) .{{ii : IsInj (view {n} i)}} →
                    inject₁ (inject₁⁻¹ i {{ii}}) ≡ i
inject₁-inject₁⁻¹ i with inj ii ← view i = refl

inject₁⁻¹-inject₁ : (j : Fin n) → inject₁⁻¹ (inject₁ j) {{inj⁺}} ≡ j
inject₁⁻¹-inject₁ j rewrite view-inj j = refl

inject₁≡⇒inject₁⁻¹≡ : ∀ {j : Fin n} {i : Fin (suc n)} (eq : inject₁ j ≡ i) →
                       inject₁⁻¹ i {{inject₁≡⁺ {eq = eq}}} ≡ j
inject₁≡⇒inject₁⁻¹≡ refl = inject₁⁻¹-inject₁ _

inject₁⁻¹-injective : (i₁ i₂ : Fin (suc n)) →
                      .{{ii₁ : IsInj (view {n} i₁)}} →
                      .{{ii₂ : IsInj (view {n} i₂)}} →
                      inject₁⁻¹ i₁ {{ii₁}} ≡ inject₁⁻¹ i₂ {{ii₂}} → i₁ ≡ i₂
inject₁⁻¹-injective i₁ i₂ with inj _ ← view i₁ | inj _ ← view i₂ = cong inject₁

toℕ-inject₁⁻¹ : (i : Fin (suc n)) .{{ii : IsInj (view {n} i)}} →
                 toℕ (inject₁⁻¹ i {{ii}}) ≡ toℕ i
toℕ-inject₁⁻¹ i with inj j ← view i = sym (toℕ-inject₁ j)

------------------------------------------------------------------------
-- Reimplementation of `Data.Fin.Base.opposite`, and its properties

-- Definition

opposite : ∀ {n} → Fin n → Fin n
opposite {suc n} i with view i
... | top   = zero
... | inj j = suc (opposite {n} j)

-- Properties

opposite-zero≡top : ∀ n → opposite {suc n} zero ≡ fromℕ n
opposite-zero≡top zero    = refl
opposite-zero≡top (suc n) = cong suc (opposite-zero≡top n)

opposite-top≡zero : ∀ n → opposite {suc n} (fromℕ n) ≡ zero
opposite-top≡zero n rewrite view-top n = refl

opposite-suc≡inject₁-opposite : ∀ {n} (j : Fin n) →
                                opposite (suc j) ≡ inject₁ (opposite j)
opposite-suc≡inject₁-opposite {suc n} i with view i
... | top   = refl
... | inj j = cong suc (opposite-suc≡inject₁-opposite {n} j)

opposite-involutive : ∀ {n} (j : Fin n) → opposite (opposite j) ≡ j
opposite-involutive {suc n} zero
  rewrite opposite-zero≡top n
        | view-top n            = refl
opposite-involutive {suc n} (suc i)
  rewrite opposite-suc≡inject₁-opposite i
        | view-inj (opposite i) = cong suc (opposite-involutive i)

opposite-suc : (j : Fin n) → toℕ (opposite (suc j)) ≡ toℕ (opposite j)
opposite-suc j = begin
  toℕ (opposite (suc j))      ≡⟨ cong toℕ (opposite-suc≡inject₁-opposite j) ⟩
  toℕ (inject₁ (opposite j))  ≡⟨ toℕ-inject₁ (opposite j) ⟩
  toℕ (opposite j)            ∎ where open ≡-Reasoning

opposite-prop : ∀ {n} (j : Fin n) → toℕ (opposite j) ≡ n ∸ suc (toℕ j)
opposite-prop {suc n} i with view i
... | top   rewrite toℕ-fromℕ n | n∸n≡0 n = refl
... | inj j = begin
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
  ... | top = Pₙ
  ... | inj j = Pᵢ₊₁⇒Pᵢ j (induct (rec _ inject₁[j]+1≤[j+1]))
    where
    inject₁[j]+1≤[j+1] : suc (toℕ (inject₁ j)) Data.Nat.Base.≤ toℕ (suc j)
    inject₁[j]+1≤[j+1] = Data.Nat.Properties.≤-reflexive (toℕ-inject₁ (suc j))
