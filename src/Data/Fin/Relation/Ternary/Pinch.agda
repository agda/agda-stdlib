------------------------------------------------------------------------
-- The Agda standard library
--
-- The '`Pinch` view' of the function `pinch` defined on finite sets
------------------------------------------------------------------------
--
-- This is an example of a view of a function defined over a datatype,
-- such that the recursion and call-pattern(s) of the function are
-- precisely mirrored in the constructors of the view type,
-- ie that we 'view the function via its graph relation'

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Relation.Ternary.Pinch where

open import Data.Fin.Base using (Fin; zero; suc; toℕ; _≤_; _<_; pinch)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; z≤n; s≤s; z<s; s<s; ∣_-_∣)
open import Data.Nat.Properties using (≤-refl; <⇒≤; ∣n-n∣≡0)
open import Data.Product using (_,_; ∃)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The View, considered as a ternary relation

-- Each constructor corresponds to a particular call-pattern in the original
-- function definition; recursive calls are represented by inductive premises

data View : ∀ {n} (i : Fin n) (j : Fin (suc n)) (k : Fin n) → Set where

  any-zero : ∀ {n} (i : Fin (suc n))             → View i zero zero
  zero-suc : ∀ {n} (j : Fin (suc n))             → View zero (suc j) j
  suc-suc  : ∀ {n} {i} {j} {k} → View {n} i j k → View (suc i) (suc j) (suc k)

-- The View is sound, ie covers all telescopes (satisfying the always-true precondition)

-- The recursion/pattern analysis of the original definition of `pinch`
-- (which is responsible for showing termination in the first place)
-- is then exactly replicated in the definition of the covering function `view`;
-- thus that definitional pattern analysis is encapsulated once and for all

view : ∀ {n} i j → View {n} i j (pinch i j)
view {suc _} i zero    = any-zero i
view   zero    (suc j) = zero-suc j
view   (suc i) (suc j) = suc-suc (view i j)

-- Interpretation of the view: the original function itself

⟦_⟧ : ∀ {i j} {k} .(v : View {n} i j k) → Fin n
⟦_⟧ {n = n} {i} {j} {k} _ = pinch i j

-- The View is complete

view-complete : ∀ {n} {i j} {k} (v : View {n} i j k) → ⟦ v ⟧ ≡ k
view-complete (any-zero i) = refl
view-complete (zero-suc j) = refl
view-complete (suc-suc v)  = cong suc (view-complete v)

------------------------------------------------------------------------
-- Properties of the function, derived from properties of the View

view-surjective : ∀ (i k : Fin n) → ∃ λ j → View i j k
view-surjective zero    k       = suc k , zero-suc k
view-surjective (suc i) zero    = zero , any-zero (suc i)
view-surjective (suc i) (suc k) with j , v ← view-surjective i k = suc j , suc-suc v

view-injective : ∀ {i j k} {p q} → View {n} i j p → View {n} i k q →
                 suc i ≢ j → suc i ≢ k → p ≡ q → j ≡ k
view-injective v w [i+1]≢j [i+1]≢k refl = aux v w [i+1]≢j [i+1]≢k where
  aux : ∀ {i j k} {r} → View {n} i j r → View {n} i k r →
        suc i ≢ j → suc i ≢ k → j ≡ k
  aux (any-zero _) (any-zero _)     [i+1]≢j [i+1]≢k = refl
  aux (any-zero _) (zero-suc .zero) [i+1]≢j [i+1]≢k with () ← [i+1]≢k refl
  aux (zero-suc _) (any-zero .zero) [i+1]≢j [i+1]≢k with () ← [i+1]≢j refl
  aux (zero-suc _) (zero-suc _)     [i+1]≢j [i+1]≢k = refl
  aux (suc-suc v)  (suc-suc w)      [i+1]≢j [i+1]≢k
    = cong suc (aux v w ([i+1]≢j ∘ cong suc) ([i+1]≢k ∘ cong suc))

view-mono-≤ : ∀ {i} {j k} {p q} → View {n} i j p → View {n} i k q →
              j ≤ k → p ≤ q
view-mono-≤ (any-zero _) _            _         = z≤n
view-mono-≤ (zero-suc _) (zero-suc _) (s≤s j≤k) = j≤k
view-mono-≤ (suc-suc v)  (suc-suc w)  (s≤s j≤k) = s≤s (view-mono-≤ v w j≤k)

view-cancel-< : ∀ {i j k} {p q} → View {n} i j p → View {n} i k q →
                p < q → j < k
view-cancel-< (any-zero _) (zero-suc _) _         = z<s
view-cancel-< (any-zero _) (suc-suc _)  _         = z<s
view-cancel-< (zero-suc _) (zero-suc _) p<q       = s<s p<q
view-cancel-< (suc-suc v)  (suc-suc w)  (s<s p<q) = s<s (view-cancel-< v w p<q)

view-j≡view-k⇒∣j-k∣≤1 : ∀ {i j k} {p q} → View {n} i j p → View {n} i k q →
                        p ≡ q → ∣ (toℕ j) - (toℕ k)∣ Nat.≤ 1
view-j≡view-k⇒∣j-k∣≤1 v w refl = aux v w
  where
    aux : ∀ {n} {i j k} {r} → View {n} i j r → View {n} i k r →
          ∣ (toℕ j) - (toℕ k) ∣ Nat.≤ 1
    aux (any-zero _)    (any-zero _)    = z≤n
    aux (any-zero zero) (zero-suc zero) = ≤-refl
    aux (zero-suc zero) (any-zero zero) = ≤-refl
    aux (zero-suc j)    (zero-suc j) rewrite ∣n-n∣≡0 (toℕ j) = z≤n
    aux (suc-suc v)     (suc-suc w) = aux v w

