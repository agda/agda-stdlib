------------------------------------------------------------------------
-- The Agda standard library
--
-- The 'punchOut view' of the function `punchOut` defined on finite sets
------------------------------------------------------------------------

-- This example of a "view of a function via its graph relation" is inspired
-- by Nathan van Doorn's recent PR#1913.

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Relation.Ternary.PunchIn where

open import Data.Fin.Base using (Fin; zero; suc; _≤_; punchIn)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat.Base using (ℕ; zero; suc; z≤n; s≤s)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)

------------------------------------------------------------------------
-- The View, considered as a ternary relation

data View : ∀ {n} (i : Fin (suc n)) (j : Fin n) (k : Fin (suc n)) → Set where

  zero-suc : ∀ {n} (j : Fin n)                   → View zero j (suc j)
  suc-zero : ∀ {n} (i : Fin (suc n))             → View (suc i) zero zero
  suc-suc  : ∀ {n} {i} {j} {k} → View {n} i j k → View (suc i) (suc j) (suc k)

-- The View enforces the codomain postcondition

Codomain : ∀ {n} (i : Fin (suc n)) (j : Fin n) → Set
Codomain i j = punchIn i j ≢ i

view-codomain : ∀ {n} {i} {j} {k} → View {n} i j k → Codomain i j
view-codomain (suc-suc v) = (view-codomain v) ∘ suc-injective

-- The View is sound, ie covers all telescopes (satisfying the always-true precondition)

view : ∀ {n} i j → View {n} i j (punchIn i j)
view zero         j  = zero-suc j
view (suc i) zero    = suc-zero i
view (suc i) (suc j) = suc-suc (view i j)

-- The View is complete

view-complete : ∀ {n} {i j} {k} (v : View {n} i j k) → k ≡ punchIn i j
view-complete (zero-suc j) = refl
view-complete (suc-zero i) = refl
view-complete (suc-suc v)  = cong suc (view-complete v)

------------------------------------------------------------------------
-- Properties of the function, derived from properties of the View

{- punchIn-mono≤ -}
j≤k⇒view-j≤view-k : ∀ {n} {i j k} {p q} → View {n} i j p → View {n} i k q →
                     j ≤ k → p ≤ q
j≤k⇒view-j≤view-k (zero-suc _) (zero-suc _)  j≤k     = s≤s j≤k
j≤k⇒view-j≤view-k (suc-zero i) _             _       = z≤n
j≤k⇒view-j≤view-k (suc-suc v)  (suc-suc w) (s≤s j≤k) = s≤s (j≤k⇒view-j≤view-k v w j≤k)

punchIn-mono≤ : ∀ {n} (i : Fin (suc n)) {j k} →
                j ≤ k → punchIn i j ≤ punchIn i k
punchIn-mono≤ i {j} {k} = j≤k⇒view-j≤view-k (view i j) (view i k)

{- punchIn-cancel≤ -}
view-j≤view-k⇒j≤k : ∀ {n} {i j k} {p q} → View {n} i j p → View {n} i k q →
                     p ≤ q → j ≤ k
view-j≤view-k⇒j≤k (zero-suc _) (zero-suc _) (s≤s p≤q) = p≤q
view-j≤view-k⇒j≤k (suc-zero i) _            _         = z≤n
view-j≤view-k⇒j≤k (suc-suc v)  (suc-suc w)  (s≤s p≤q) = s≤s (view-j≤view-k⇒j≤k v w p≤q)

punchIn-cancel≤ : ∀ {n} (i : Fin (suc n)) {j k} →
                  (punchIn i j ≤ punchIn i k) → j ≤ k
punchIn-cancel≤ i {j} {k} = view-j≤view-k⇒j≤k (view i j) (view i k)

