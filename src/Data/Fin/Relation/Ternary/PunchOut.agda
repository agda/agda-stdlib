------------------------------------------------------------------------
-- The Agda standard library
--
-- The '`PunchOut` view of the function `punchOut` defined on finite sets
------------------------------------------------------------------------
--
-- This is an example of a view of a function defined over a datatype,
-- such that the recursion and call-pattern(s) of the function are
-- precisely mirrored in the constructors of the view type,
-- ie that we 'view the function via its graph relation'

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Relation.Ternary.PunchOut where

open import Data.Fin.Base using (Fin; zero; suc; _≤_; punchOut)
open import Data.Fin.Properties using (suc-injective)
open import Data.Fin.Relation.Ternary.PunchIn as PunchIn using ()
open import Data.Nat.Base using (ℕ; zero; suc; z≤n; s≤s)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The View, considered as a ternary relation

-- Each constructor corresponds to a particular call-pattern in the original
-- function definition; recursive calls are represented by inductive premises

data View : ∀ {n} (i j : Fin (suc n)) (k : Fin n) → Set where

  zero-suc : ∀ {n} (j : Fin n)                   → View zero (suc j) j
  suc-zero : ∀ {n} (i : Fin (suc n))             → View (suc i) zero zero
  suc-suc  : ∀ {n} {i} {j} {k} → View {n} i j k → View (suc i) (suc j) (suc k)

-- The View enforces the precondition given by a Domain predicate

Domain : ∀ (i j : Fin (suc n)) → Set
Domain i j = i ≢ j

view-domain : ∀ {i j} {k} → View {n} i j k → Domain i j
view-domain (suc-suc v) = (view-domain v) ∘ suc-injective

-- The View is sound, ie covers all telescopes satisfying that precondition

-- The recursion/pattern analysis of the original definition of `punchOut`
-- (which is responsible for showing termination in the first place)
-- is then exactly replicated in the definition of the covering function `view`;
-- thus that definitional pattern analysis is encapsulated once and for all

view : ∀ {n} {i j} (d : Domain i j) → View {n} i j (punchOut d)
view             {i = zero}  {j = zero}  d with () ← d refl
view             {i = zero}  {j = suc j} d = zero-suc j
view {n = suc _} {i = suc i} {j = zero}  d = suc-zero i
view {n = suc _} {i = suc i} {j = suc j} d = suc-suc (view (d ∘ (cong suc)))

-- Interpretation of the view: the original function itself

⟦_⟧ : ∀ {i j} {k} (v : View {n} i j k) → Fin n
⟦ v ⟧ = punchOut (view-domain v)

-- The View is complete

view-complete : ∀ {i j} {k} (v : View {n} i j k) → ⟦ v ⟧ ≡ k
view-complete (zero-suc j) = refl
view-complete (suc-zero i) = refl
view-complete (suc-suc v)  = cong suc (view-complete v)

------------------------------------------------------------------------
-- Properties of the function, derived from properties of the View

view-cong : ∀ {i j k} {p q} →
                 View {n} i j p → View {n} i k q → j ≡ k → p ≡ q
view-cong v w refl = aux v w where
  aux : ∀ {i j} {p q} → View {n} i j p → View {n} i j q → p ≡ q
  aux (zero-suc _) (zero-suc _) = refl
  aux (suc-zero i) (suc-zero i) = refl
  aux (suc-suc v)  (suc-suc w)  = cong suc (aux v w)

view-injective : ∀ {i j k} {p q} →
                 View {n} i j p → View {n} i k q → p ≡ q → j ≡ k
view-injective v w refl = aux v w where
  aux : ∀ {i j k} {r} → View {n} i j r → View {n} i k r → j ≡ k
  aux (zero-suc _) (zero-suc _) = refl
  aux (suc-zero i) (suc-zero i) = refl
  aux (suc-suc v)  (suc-suc w)  = cong suc (aux v w)

view-mono-≤ : ∀ {i j k} {p q} → View {n} i j p → View {n} i k q →
              j ≤ k → p ≤ q
view-mono-≤ (zero-suc j) (zero-suc k)  (s≤s j≤k) = j≤k
view-mono-≤ (suc-zero i) _             _         = z≤n
view-mono-≤ (suc-suc vj) (suc-suc vk)  (s≤s j≤k) = s≤s (view-mono-≤ vj vk j≤k)

view-cancel-≤ : ∀ {i j k} {p q} → View {n} i j p → View {n} i k q →
                p ≤ q → j ≤ k
view-cancel-≤ (zero-suc j) (zero-suc k)  p≤q       = s≤s p≤q
view-cancel-≤ (suc-zero i) _             _         = z≤n
view-cancel-≤ (suc-suc vj) (suc-suc vk)  (s≤s p≤q) = s≤s (view-cancel-≤ vj vk p≤q)

-- PunchOut.View and PunchIn.View are mutual converses

view-view⁻¹ : ∀ {i j} {k} → View {n} i j k → PunchIn.View {n} i k j
view-view⁻¹ (zero-suc _) = PunchIn.zero-suc _
view-view⁻¹ (suc-zero i) = PunchIn.suc-zero i
view-view⁻¹ (suc-suc v)  = PunchIn.suc-suc (view-view⁻¹ v)

view⁻¹-view : ∀ {i j} {k} → PunchIn.View {n} i k j → View {n} i j k
view⁻¹-view (PunchIn.zero-suc _) = zero-suc _
view⁻¹-view (PunchIn.suc-zero i) = suc-zero i
view⁻¹-view (PunchIn.suc-suc v)  = suc-suc (view⁻¹-view v)
