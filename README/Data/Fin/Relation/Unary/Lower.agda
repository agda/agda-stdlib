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

open import Data.Nat.Base using (ℕ; zero; suc; pred)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; inject₁)
open import Data.Fin.Properties
  using (toℕ-fromℕ; toℕ-inject₁; toℕ-inject₁-≢; inject₁-injective)
import Data.Fin.Relation.Unary.Top as Top
open import Level using (Level)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)

private
  variable
    ℓ : Level
    n : ℕ
    i j : Fin n

------------------------------------------------------------------------
-- Derived induction principles from the Top view, via another view!

-- The idea being, that in what follows, a call pattern is repeated over
-- and over again, so should be reified as induction over a revised view,
-- obtained from `Top.view` by restricting the domain

data View : {i : Fin (suc n)} → n ≢ toℕ i → Set where
  ‵inject₁ : (j : Fin n) {n≢j : n ≢ toℕ (inject₁ j)} → View n≢j

view : {i : Fin (suc n)} (n≢i : n ≢ toℕ i) → View n≢i
view {i = i} n≢i with Top.view i
... | Top.‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i
... | Top.‵inject₁ j = ‵inject₁ j


------------------------------------------------------------------------
-- Reimplementation of `Data.Fin.Base.lower₁` and its properties,
-- together with the streamlined versions obtained from the view. 

-- definition of lower₁/inject₁⁻¹

lower₁ : ∀ (i : Fin (suc n)) → n ≢ toℕ i → Fin n
lower₁ i n≢i with Top.view i
... | Top.‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i
... | Top.‵inject₁ j = j

inject₁⁻¹ : ∀ (i : Fin (suc n)) → (n ≢ toℕ i) → Fin n
inject₁⁻¹ i n≢i with ‵inject₁ j ← view n≢i = j

------------------------------------------------------------------------
-- properties of lower₁/inject₁⁻¹

toℕ-lower₁ : ∀ i (n≢i : n ≢ toℕ i) → toℕ (lower₁ i n≢i) ≡ toℕ i
toℕ-lower₁ i n≢i with Top.view i
... | Top.‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i
... | Top.‵inject₁ j = sym (toℕ-inject₁ j)

toℕ-inject₁⁻¹ : ∀ i (n≢i : n ≢ toℕ i) → toℕ (inject₁⁻¹ i n≢i) ≡ toℕ i
toℕ-inject₁⁻¹ i n≢i with ‵inject₁ j ← view n≢i = sym (toℕ-inject₁ j)

lower₁-injective : ∀ {n≢i : n ≢ toℕ i} {n≢j : n ≢ toℕ j} →
                   lower₁ i n≢i ≡ lower₁ j n≢j → i ≡ j
lower₁-injective {i = i} {j = j} {n≢i} {n≢j} eq with Top.view i
... | Top.‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i
... | Top.‵inject₁ _ with Top.view j
... | Top.‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢j
... | Top.‵inject₁ _ = cong inject₁ eq

inject₁⁻¹-injective : ∀ {n≢i : n ≢ toℕ i} {n≢j : n ≢ toℕ j} →
                   inject₁⁻¹ i n≢i ≡ inject₁⁻¹ j n≢j → i ≡ j
inject₁⁻¹-injective {i = i} {j = j} {n≢i} {n≢j} eq
  with ‵inject₁ _ ← view n≢i | ‵inject₁ _ ← view n≢j = cong inject₁ eq

lower₁-irrelevant : ∀ (i : Fin (suc n)) (n≢i₁ n≢i₂ : n ≢ toℕ i) →
                    lower₁ i n≢i₁ ≡ lower₁ i n≢i₂
lower₁-irrelevant i n≢i₁ n≢i₂ with Top.view i
... | Top.‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i₁
... | Top.‵inject₁ _ = refl

-- here we need/use a helper function, in order to avoid having
-- to appeal to injectivity of inject₁ in the unifier
inject₁⁻¹-irrelevant′ : ∀ {i j : Fin (suc n)} (i≡j : i ≡ j) →
                        (n≢i : n ≢ toℕ i) (n≢j : n ≢ toℕ j) →
                        inject₁⁻¹ i n≢i ≡ inject₁⁻¹ j n≢j
inject₁⁻¹-irrelevant′ eq n≢i n≢j
  with ‵inject₁ _ ← view n≢i | ‵inject₁ _ ← view n≢j = inject₁-injective eq

inject₁⁻¹-irrelevant : ∀ (i : Fin (suc n)) (n≢i₁ n≢i₂ : n ≢ toℕ i) →
                       inject₁⁻¹ i n≢i₁ ≡ inject₁⁻¹ i n≢i₂
inject₁⁻¹-irrelevant i = inject₁⁻¹-irrelevant′ refl

------------------------------------------------------------------------
-- inject₁ and lower₁/inject₁⁻¹

inject₁-lower₁ : ∀ (i : Fin (suc n)) (n≢i : n ≢ toℕ i) →
                 inject₁ (lower₁ i n≢i) ≡ i
inject₁-lower₁ i n≢i with Top.view i
... | Top.‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i
... | Top.‵inject₁ _ = refl

inject₁-inject₁⁻¹ : ∀ (i : Fin (suc n)) (n≢i : n ≢ toℕ i) →
                 inject₁ (inject₁⁻¹ i n≢i) ≡ i
inject₁-inject₁⁻¹ i n≢i with ‵inject₁ _ ← view n≢i = refl

inject₁≡⇒lower₁≡ : {i : Fin (ℕ.suc n)} (n≢i : n ≢ toℕ i) →
                   inject₁ j ≡ i → lower₁ i n≢i ≡ j
inject₁≡⇒lower₁≡ {i = i} n≢i inject₁[j]≡i  with Top.view i
... | Top.‵fromℕ {n} = contradiction (sym (toℕ-fromℕ n)) n≢i
... | Top.‵inject₁ _ = sym (inject₁-injective inject₁[j]≡i)

inject₁≡⇒inject₁⁻¹≡ : {i : Fin (ℕ.suc n)} (n≢i : n ≢ toℕ i) →
                      inject₁ j ≡ i → inject₁⁻¹ i n≢i ≡ j
inject₁≡⇒inject₁⁻¹≡ {i = i} n≢i inject₁[j]≡i  with ‵inject₁ _ ← view n≢i
  = sym (inject₁-injective inject₁[j]≡i)

lower₁-inject₁ : ∀ (i : Fin n) →
                 lower₁ (inject₁ i) (toℕ-inject₁-≢ i) ≡ i
lower₁-inject₁ {n} i = inject₁≡⇒lower₁≡ (toℕ-inject₁-≢ i) refl

inject₁⁻¹-inject₁ : ∀ (i : Fin n) →
                    inject₁⁻¹ (inject₁ i) (toℕ-inject₁-≢ i) ≡ i
inject₁⁻¹-inject₁ {n} i = inject₁≡⇒inject₁⁻¹≡ (toℕ-inject₁-≢ i) refl

