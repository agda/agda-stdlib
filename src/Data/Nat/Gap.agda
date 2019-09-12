------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on "gaps" between numbers.
--
-- This module defines a number of operations for computing on the
-- "gap" in the type _≤′_. The usual proof that n ≤ m is encoded like
-- so:
--
--   data _≤_ : Rel ℕ 0ℓ where
--     z≤n : ∀ {n}                 → zero  ≤ n
--     s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n
--
-- In other words, the inductive structure of the proof follows the
-- structure of the first index.
--
-- In contrast, _≤′_ is encoded like so:
--
--   data _≤′_ (m : ℕ) : ℕ → Set where
--     ≤′-refl :                         m ≤′ m
--     ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n
--
-- Here, the inductive structure of the proof of m ≤′ n follows the ℕ
-- n - m. This module provides functions which give proofs relevant to
-- m, while computing on n - m. If n - m is much smaller than m this
-- can result in a significant performance improvement.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Gap where

open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Nat.Base using (_≤′_; ≤′-refl; ≤′-step; _<′_) public
open import Data.Nat.Properties using (≤′-trans) public
open import Function
open import Data.Fin as Fin using (Fin)

data InjectionOrdering {n : ℕ} : ∀ {i j}
                      → (i≤n : i ≤′ n)
                      → (j≤n : j ≤′ n)
                      → Set
                      where
  inj-lt : ∀ {i j-1}
     → (i≤j-1 : i ≤′ j-1)
     → (j≤n : suc j-1 ≤′ n)
     → InjectionOrdering (≤′-step i≤j-1 ⟨ ≤′-trans ⟩ j≤n) j≤n
  inj-gt : ∀ {i-1 j}
     → (i≤n : suc i-1 ≤′ n)
     → (j≤i-1 : j ≤′ i-1)
     → InjectionOrdering i≤n (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n)
  inj-eq : ∀ {i} → (i≤n : i ≤′ n) → InjectionOrdering i≤n i≤n

inj-compare : ∀ {i j n}
    → (x : i ≤′ n)
    → (y : j ≤′ n)
    → InjectionOrdering x y
inj-compare ≤′-refl ≤′-refl = inj-eq ≤′-refl
inj-compare ≤′-refl (≤′-step y) = inj-gt ≤′-refl y
inj-compare (≤′-step x) ≤′-refl = inj-lt x ≤′-refl
inj-compare (≤′-step x) (≤′-step y) = case inj-compare x y of
    λ { (inj-lt i≤j-1 .y) → inj-lt i≤j-1 (≤′-step y)
      ; (inj-gt .x j≤i-1) → inj-gt (≤′-step x) j≤i-1
      ; (inj-eq .x) → inj-eq (≤′-step x)
      }

space : ∀ {n} → Fin n → ℕ
space f = suc (go f)
  where
  go : ∀ {n} → Fin n → ℕ
  go {suc n} Fin.zero = n
  go (Fin.suc x) = go x

Fin⇒≤ : ∀ {n} (x : Fin n) → space x ≤′ n
Fin⇒≤ Fin.zero = ≤′-refl
Fin⇒≤ (Fin.suc x) = ≤′-step (Fin⇒≤ x)
