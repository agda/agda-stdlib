------------------------------------------------------------------------
-- The Agda standard library
--
-- The 'punchOut view' of the function `punchOut` defined on finite sets
------------------------------------------------------------------------

-- This example of a "view of a function via its graph relation" is inspired
-- by Nathan van Doorn's recent PR#1913.

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Relation.Ternary.PunchOut where

open import Data.Fin.Base using (Fin; zero; suc; _≤_; punchOut)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat.Base using (ℕ; zero; suc; z≤n; s≤s)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)

------------------------------------------------------------------------
-- The View, considered as a ternary relation

data View : ∀ {n} (i j : Fin (suc n)) (k : Fin n) → Set where

  zero-suc : ∀ {n} (j : Fin n)                   → View zero (suc j) j
  suc-zero : ∀ {n} (i : Fin (suc n))             → View (suc i) zero zero
  suc-suc  : ∀ {n} {i} {j} {k} → View {n} i j k → View (suc i) (suc j) (suc k)

-- The View enforces the precondition given by a Domain predicate

Domain : ∀ {n} (i j : Fin (suc n)) → Set
Domain i j = i ≢ j

view-domain : ∀ {n} {i j} {k} → View {n} i j k → Domain i j
view-domain (suc-suc v) = (view-domain v) ∘ suc-injective

-- The View is sound, ie covers all telescopes satisfying that precondition

view : ∀ {n} {i j} (d : Domain i j) → View {n} i j (punchOut d)
view             {i = zero}  {j = zero}  d with () ← d refl
view             {i = zero}  {j = suc j} d = zero-suc j
view {n = suc _} {i = suc i} {j = zero}  d = suc-zero i
view {n = suc _} {i = suc i} {j = suc j} d = suc-suc (view (d ∘ (cong suc)))

-- The View is complete

view-complete : ∀ {n} {i j} {k} (v : View {n} i j k) → k ≡ punchOut (view-domain v)
view-complete (zero-suc j) = refl
view-complete (suc-zero i) = refl
view-complete (suc-suc v)  = cong suc (view-complete v)

------------------------------------------------------------------------
-- Properties of the function, derived from properties of the View

{- punchOut-mono≤ -}
j≤k⇒view-j≤view-k : ∀ {n} {i j k} {p q} → View {n} i j p → View {n} i k q →
                     j ≤ k → p ≤ q
j≤k⇒view-j≤view-k (zero-suc j) (zero-suc k)  (s≤s j≤k) = j≤k
j≤k⇒view-j≤view-k (suc-zero i) _             _         = z≤n
j≤k⇒view-j≤view-k (suc-suc vj) (suc-suc vk)  (s≤s j≤k) = s≤s (j≤k⇒view-j≤view-k vj vk j≤k)

punchOut-mono≤ : ∀ {n} {i j k : Fin (suc n)} (i≢j : i ≢ j) (i≢k : i ≢ k) →
                 j ≤ k → punchOut i≢j ≤ punchOut i≢k
punchOut-mono≤ i≢j i≢k = j≤k⇒view-j≤view-k (view i≢j) (view i≢k)

{- punchOut-cancel≤ -}
view-j≤view-k⇒j≤k : ∀ {n} {i j k} {p q} → View {n} i j p → View {n} i k q →
                     p ≤ q → j ≤ k
view-j≤view-k⇒j≤k (zero-suc j) (zero-suc k)  p≤q       = s≤s p≤q
view-j≤view-k⇒j≤k (suc-zero i) _             _         = z≤n
view-j≤view-k⇒j≤k (suc-suc vj) (suc-suc vk)  (s≤s p≤q) = s≤s (view-j≤view-k⇒j≤k vj vk p≤q)

punchOut-cancel≤ : ∀ {n} {i j k : Fin (suc n)} (i≢j : i ≢ j) (i≢k : i ≢ k) →
                   (p≤q : punchOut i≢j ≤ punchOut i≢k) →  j ≤ k
punchOut-cancel≤ i≢j i≢k = view-j≤view-k⇒j≤k (view i≢j) (view i≢k)

