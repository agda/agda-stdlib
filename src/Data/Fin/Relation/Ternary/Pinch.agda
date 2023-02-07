------------------------------------------------------------------------
-- The Agda standard library
--
-- The 'punchOut view' of the function `punchOut` defined on finite sets
------------------------------------------------------------------------

-- This example of a "view of a function via its graph relation" is inspired
-- by Nathan van Doorn's recent PR#1913.

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Relation.Ternary.Pinch where

open import Data.Fin.Base using (Fin; zero; suc; toℕ; _≤_; _<_; pinch)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; z≤n; s≤s; z<s; s<s; ∣_-_∣)
open import Data.Nat.Properties using (≤-refl; <⇒≤; ∣n-n∣≡0)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)

------------------------------------------------------------------------
-- The View, considered as a ternary relation

data View : ∀ {n} (i : Fin n) (j : Fin (suc n)) (k : Fin n) → Set where

  any-zero : ∀ {n} (i : Fin (suc n))             → View i zero zero
  zero-suc : ∀ {n} (j : Fin (suc n))             → View zero (suc j) j
  suc-suc  : ∀ {n} {i} {j} {k} → View {n} i j k → View (suc i) (suc j) (suc k)

-- The View is sound, ie covers all telescopes (satisfying the always-true precondition)

view : ∀ {n} i j → View {n} i j (pinch i j)
view {suc _} i zero    = any-zero i
view   zero    (suc j) = zero-suc j
view   (suc i) (suc j) = suc-suc (view i j)

-- The View is complete

view-complete : ∀ {n} {i j} {k} (v : View {n} i j k) → k ≡ pinch i j
view-complete (any-zero i) = refl
view-complete (zero-suc j) = refl
view-complete (suc-suc v)  = cong suc (view-complete v)

------------------------------------------------------------------------
-- Properties of the function, derived from properties of the View

{- pinch-mono≤ -}
j≤k⇒view-j≤view-k : ∀ {n} {i} {j k} {p q} → View {n} i j p → View {n} i k q →
                     j ≤ k → p ≤ q
j≤k⇒view-j≤view-k (any-zero _) _            _         = z≤n
j≤k⇒view-j≤view-k (zero-suc _) (zero-suc _) (s≤s j≤k) = j≤k
j≤k⇒view-j≤view-k (suc-suc v)  (suc-suc w)  (s≤s j≤k) = s≤s (j≤k⇒view-j≤view-k v w j≤k)

pinch-mono≤ : ∀ {n} (i : Fin n) {j k} →
                j ≤ k → pinch i j ≤ pinch i k
pinch-mono≤ i {j} {k} = j≤k⇒view-j≤view-k (view i j) (view i k)

{- pinch-cancel< -}
view-j<view-k⇒j<k : ∀ {n} {i j k} {p q} → View {n} i j p → View {n} i k q →
                     p < q → j < k
view-j<view-k⇒j<k (any-zero _) (zero-suc _) _         = z<s
view-j<view-k⇒j<k (any-zero _) (suc-suc _)  _         = z<s
view-j<view-k⇒j<k (zero-suc _) (zero-suc _) p<q       = s<s p<q
view-j<view-k⇒j<k (suc-suc v)  (suc-suc w)  (s<s p<q) = s<s (view-j<view-k⇒j<k v w p<q)

pinch-cancel< : ∀ {n} (i : Fin (suc n)) {j k} →
                  (pinch i j < pinch i k) → j < k
pinch-cancel< i {j} {k} = view-j<view-k⇒j<k (view i j) (view i k)

{- pinch-cancel≡ -}
view-j≡view-k⇒∣j-k∣≤1 : ∀ {n} {i j k} {p q} → View {n} i j p → View {n} i k q →
                        p ≡ q → ∣ (toℕ j) - (toℕ k)∣ Nat.≤ 1
view-j≡view-k⇒∣j-k∣≤1 v w refl = helper v w
  where
    helper : ∀ {n} {i j k} {r} → View {n} i j r → View {n} i k r →
             ∣ (toℕ j) - (toℕ k) ∣ Nat.≤ 1
    helper (any-zero _)    (any-zero _)    = z≤n
    helper (any-zero zero) (zero-suc zero) = ≤-refl
    helper (zero-suc zero) (any-zero zero) = ≤-refl
    helper (zero-suc j)    (zero-suc j) rewrite ∣n-n∣≡0 (toℕ j) = z≤n
    helper (suc-suc v)     (suc-suc w) = helper v w

pinch-cancel≡ : ∀ {n} (i : Fin n) {j k} →
                (pinch i j ≡ pinch i k) → ∣ (toℕ j) - (toℕ k) ∣ Nat.≤ 1
pinch-cancel≡ i {j} {k} = view-j≡view-k⇒∣j-k∣≤1 (view i j) (view i k)

