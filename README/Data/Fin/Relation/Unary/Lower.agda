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

--- NB this is a provisional commit, ahead of merging PR #1923

{-# OPTIONS --cubical-compatible --safe #-}

module README.Data.Fin.Relation.Unary.Lower where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; inject₁)
open import Data.Fin.Properties
  using (toℕ-fromℕ; toℕ-inject₁; toℕ-inject₁-≢; inject₁-injective)
open import Data.Fin.Relation.Unary.TopREVISED
open import Level using (Level)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (Pred)

private
  variable
    ℓ : Level
    n : ℕ
    i j : Fin n

------------------------------------------------------------------------
-- Derived induction principle

module _ (P : ∀ {n} → Pred (Fin (suc n)) ℓ) where

  view-inject₁-case : (Pinject₁[_] : (j : Fin n) → P (inject₁ j)) →
                      ∀ {i : Fin (suc n)} → n ≢ toℕ i → P i
  view-inject₁-case Pinject₁[_] {i} n≢i with view i
  ... | ‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i
  ... | ‵inject₁ j = Pinject₁[ j ]


------------------------------------------------------------------------
-- Reimplementation of `Data.Fin.Base.lower₁` and its properties

-- definition of lower₁

lower₁ : ∀ (i : Fin (suc n)) → n ≢ toℕ i → Fin n
lower₁ i n≢i with view i
... | ‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i
... | ‵inject₁ j = j

------------------------------------------------------------------------
-- properties of lower₁

toℕ-lower₁ : ∀ i (n≢i : n ≢ toℕ i) → toℕ (lower₁ i n≢i) ≡ toℕ i
toℕ-lower₁ i n≢i with view i
... | ‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i
... | ‵inject₁ j = sym (toℕ-inject₁ j)

lower₁-injective : ∀ {n≢i : n ≢ toℕ i} {n≢j : n ≢ toℕ j} →
                   lower₁ i n≢i ≡ lower₁ j n≢j → i ≡ j
lower₁-injective {i = i} {j = j} {n≢i} {n≢j} eq with view i
... | ‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i
... | ‵inject₁ i₁ with view j
... | ‵fromℕ {n}  = contradiction (sym (toℕ-fromℕ n)) n≢j
... | ‵inject₁ j₁ = cong inject₁ eq

lower₁-irrelevant : ∀ (i : Fin (suc n)) (n≢i₁ n≢i₂ : n ≢ toℕ i) →
                    lower₁ i n≢i₁ ≡ lower₁ i n≢i₂
lower₁-irrelevant i n≢i₁ n≢i₂ with view i
... | ‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i₁
... | ‵inject₁ j = refl

------------------------------------------------------------------------
-- inject₁ and lower₁

inject₁-lower₁ : ∀ (i : Fin (suc n)) (n≢i : n ≢ toℕ i) →
                 inject₁ (lower₁ i n≢i) ≡ i
inject₁-lower₁ i n≢i with view i
... | ‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i
... | ‵inject₁ j = refl

inject₁≡⇒lower₁≡ : {j : Fin (ℕ.suc n)} (n≢j : n ≢ toℕ j) →
                   inject₁ i ≡ j → lower₁ j n≢j ≡ i
inject₁≡⇒lower₁≡ {j = j} n≢j inject₁[i]≡j  with view j
... | ‵fromℕ {n}  = contradiction (sym (toℕ-fromℕ n)) n≢j
... | ‵inject₁ j₁ = sym (inject₁-injective inject₁[i]≡j)

lower₁-inject₁ : ∀ (i : Fin n) →
                 lower₁ (inject₁ i) (toℕ-inject₁-≢ i) ≡ i
lower₁-inject₁ {n} i = inject₁≡⇒lower₁≡ (toℕ-inject₁-≢ i) refl

