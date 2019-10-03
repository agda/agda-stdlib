------------------------------------------------------------------------
-- The Agda standard library
--
-- Component functions of permutations found in `Data.Fin.Permutation`
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Permutation.Components where

open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat as ℕ using (zero; suc; _∸_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (proj₂)
open import Relation.Nullary using (dec; isYes; yes; no)
open import Relation.Nullary.Decidable using (dec-true; dec-false)
open import Relation.Nullary.Reflects as Ref using (invert)
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties using (Involutive)
open ≡-Reasoning

--------------------------------------------------------------------------------
--  Functions
--------------------------------------------------------------------------------

-- 'tranpose i j' swaps the places of 'i' and 'j'.

transpose : ∀ {n} → Fin n → Fin n → Fin n → Fin n
transpose i j k = if isYes (k ≟ i)
  then j
  else if isYes (k ≟ j)
    then i
    else k

-- reverse i = n ∸ 1 ∸ i

reverse : ∀ {n} → Fin n → Fin n
reverse {suc n} i  = inject≤ (n ℕ- i) (ℕₚ.n∸m≤n (toℕ i) (suc n))

--------------------------------------------------------------------------------
--  Properties
--------------------------------------------------------------------------------

transpose-inverse : ∀ {n} (i j : Fin n) {k} →
                    transpose i j (transpose j i k) ≡ k
transpose-inverse i j {k} with k ≟ j
... | dec true  [k=j] rewrite dec-true (i ≟ i) refl = sym (invert [k=j])
... | dec false [k≠j] with k ≟ i
...   | dec false [k≠i] rewrite dec-false (k ≟ i) (invert [k≠i])
                              | dec-false (k ≟ j) (invert [k≠j]) = refl
...   | dec true  [k=i] with j ≟ i
...     | dec true  [j=i] = trans (invert [j=i]) (sym (invert [k=i]))
...     | dec false [j≠i] rewrite dec-true (j ≟ j) refl = sym (invert [k=i])

reverse-prop : ∀ {n} → (i : Fin n) → toℕ (reverse i) ≡ n ∸ suc (toℕ i)
reverse-prop {suc n} i = begin
  toℕ (inject≤ (n ℕ- i) _)  ≡⟨ toℕ-inject≤ _ _ ⟩
  toℕ (n ℕ- i)              ≡⟨ toℕ‿ℕ- n i ⟩
  n ∸ toℕ i                 ∎

reverse-involutive : ∀ {n} → Involutive _≡_ (reverse {n})
reverse-involutive {suc n} i = toℕ-injective (begin
  toℕ (reverse (reverse i)) ≡⟨ reverse-prop (reverse i) ⟩
  n ∸ (toℕ (reverse i))     ≡⟨ cong (n ∸_) (reverse-prop i) ⟩
  n ∸ (n ∸ (toℕ i))         ≡⟨ ℕₚ.m∸[m∸n]≡n (ℕₚ.≤-pred (toℕ<n i)) ⟩
  toℕ i                     ∎)

reverse-suc : ∀ {n} {i : Fin n} → toℕ (reverse (suc i)) ≡ toℕ (reverse i)
reverse-suc {n} {i} = begin
  toℕ (reverse (suc i))      ≡⟨ reverse-prop (suc i) ⟩
  suc n ∸ suc (toℕ (suc i))  ≡⟨⟩
  n ∸ toℕ (suc i)            ≡⟨⟩
  n ∸ suc (toℕ i)            ≡⟨ sym (reverse-prop i) ⟩
  toℕ (reverse i)            ∎
