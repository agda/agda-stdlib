------------------------------------------------------------------------
-- The Agda standard library
--
-- The '`PunchIn` view' of the function `punchIn` defined on finite sets
------------------------------------------------------------------------
--
-- This is an example of a view of a function defined over a datatype,
-- such that the recursion and call-pattern(s) of the function are
-- precisely mirrored in the constructors of the view type,
-- ie that we 'view the function via its graph relation'

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Relation.Ternary.PunchIn where

open import Data.Fin.Base using (Fin; zero; suc; _≤_; punchIn)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat.Base using (ℕ; zero; suc; z≤n; s≤s)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The View, considered as a ternary relation

data View : ∀ {n} (i : Fin (suc n)) (j : Fin n) (k : Fin (suc n)) → Set where

  zero-suc : ∀ {n} (j : Fin n)                   → View zero j (suc j)
  suc-zero : ∀ {n} (i : Fin (suc n))             → View (suc i) zero zero
  suc-suc  : ∀ {n} {i} {j} {k} → View {n} i j k → View (suc i) (suc j) (suc k)

-- The View enforces the codomain postcondition

Codomain : ∀ (i : Fin (suc n)) (j : Fin n) → Set
Codomain i j = punchIn i j ≢ i

view-codomain : ∀ {i} {j} {k} → View {n} i j k → Codomain i j
view-codomain (suc-suc v) = (view-codomain v) ∘ suc-injective

-- The View is sound, ie covers all telescopes (satisfying the always-true precondition)

view : ∀ i j → View {n} i j (punchIn i j)
view zero         j  = zero-suc j
view (suc i) zero    = suc-zero i
view (suc i) (suc j) = suc-suc (view i j)

-- The View is complete

view-complete : ∀ {i j} {k} (v : View {n} i j k) → punchIn i j ≡ k
view-complete (zero-suc j) = refl
view-complete (suc-zero i) = refl
view-complete (suc-suc v)  = cong suc (view-complete v)

------------------------------------------------------------------------
-- Properties of the View

view-injective : ∀ {i j k} {p q} →
                 View {n} i j p → View {n} i k q → p ≡ q → j ≡ k
view-injective v w refl = aux v w where
  aux : ∀ {i j k} {r} → View {n} i j r → View {n} i k r → j ≡ k
  aux (zero-suc _) (zero-suc _) = refl
  aux (suc-zero i) (suc-zero i) = refl
  aux (suc-suc v) (suc-suc w)   = cong suc (aux v w)

view-mono-≤ : ∀ {i j k} {p q} → View {n} i j p → View {n} i k q →
              j ≤ k → p ≤ q
view-mono-≤ (zero-suc _) (zero-suc _)  j≤k     = s≤s j≤k
view-mono-≤ (suc-zero i) _             _       = z≤n
view-mono-≤ (suc-suc v)  (suc-suc w) (s≤s j≤k) = s≤s (view-mono-≤ v w j≤k)

view-cancel-≤ : ∀ {i j k} {p q} → View {n} i j p → View {n} i k q →
                p ≤ q → j ≤ k
view-cancel-≤ (zero-suc _) (zero-suc _) (s≤s p≤q) = p≤q
view-cancel-≤ (suc-zero i) _            _         = z≤n
view-cancel-≤ (suc-suc v)  (suc-suc w)  (s≤s p≤q) = s≤s (view-cancel-≤ v w p≤q)

