------------------------------------------------------------------------
-- The Agda standard library
--
-- Decomposition of permutations into a list of transpositions.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Permutation.Transposition.List where

open import Data.Fin.Base
open import Data.Fin.Permutation
import Data.Fin.Permutation.Components as PC
import Data.List as L
open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; trans; sym; →-to-⟶; cong; cong₂)
open P.≡-Reasoning


------------------------------------------------------------------------
-- Types

TranspositionList : ℕ → Set
TranspositionList n = L.List (Fin n × Fin n)

------------------------------------------------------------------------
-- Operations on transposition lists

evalₜ : ∀ {n} → TranspositionList n → Permutation′ n
evalₜ L.[] = id
evalₜ ((i , j) L.∷ xs) = (transpose i j) ∘ₚ (evalₜ xs)

liftₜ : ∀ {n} → TranspositionList n → TranspositionList (suc n)
liftₜ xs = L.map (λ (i , j) → (suc i , suc j)) xs

------------------------------------------------------------------------
-- Decomposition of a permutation into transpositions

-- This decomposition is not a unique representation of the original
-- permutation but can be used to simply proofs about permutations (by
-- instead inducting on the list of transpositions).

decompose : ∀ {n} → Permutation′ n → TranspositionList n
decompose {zero} π = L.[]
decompose {suc n} π = (π ⟨$⟩ˡ zero , zero) L.∷ liftₜ (decompose (remove zero ((transpose zero (π ⟨$⟩ˡ zero)) ∘ₚ π)))

------------------------------------------------------------------------
-- Properties

eval-lift : ∀ {n} → (xs : TranspositionList n) → ∀ i → evalₜ (liftₜ xs) ⟨$⟩ʳ i ≡ lift₀ (evalₜ xs) ⟨$⟩ʳ i
eval-lift L.[] = sym ∘ lift-id
eval-lift ((i , j) L.∷ xs) k = begin
  transpose (suc i) (suc j) ∘ₚ evalₜ (liftₜ xs) ⟨$⟩ʳ k ≡⟨ cong (evalₜ (liftₜ xs) ⟨$⟩ʳ_) (lift-transpose i j k) ⟩
  lift₀ (transpose i j) ∘ₚ evalₜ (liftₜ xs) ⟨$⟩ʳ k     ≡⟨ eval-lift xs (lift₀ (transpose i j) ⟨$⟩ʳ k) ⟩
  lift₀ (evalₜ xs) ⟨$⟩ʳ (lift₀ (transpose i j) ⟨$⟩ʳ k) ≡⟨ lift-comp (transpose i j) (evalₜ xs) k ⟩
  lift₀ (transpose i j ∘ₚ evalₜ xs) ⟨$⟩ʳ k             ∎

eval-decompose : ∀ {n} → (π : Permutation′ n) → ∀ i → evalₜ (decompose π) ⟨$⟩ʳ i ≡ π ⟨$⟩ʳ i
eval-decompose {zero} π ()
eval-decompose {suc n} π i = begin
  tπ0 ∘ₚ evalₜ (liftₜ (decompose (remove zero (t0π ∘ₚ π)))) ⟨$⟩ʳ i ≡⟨ eval-lift (decompose (remove zero (t0π ∘ₚ π))) (tπ0 ⟨$⟩ʳ i) ⟩
  tπ0 ∘ₚ lift₀ (evalₜ (decompose (remove zero (t0π ∘ₚ π)))) ⟨$⟩ʳ i ≡⟨ lift-cong _ _ (eval-decompose _) (tπ0 ⟨$⟩ʳ i) ⟩
  tπ0 ∘ₚ lift₀ (remove zero (t0π ∘ₚ π)) ⟨$⟩ʳ i                     ≡⟨ lift-remove (t0π ∘ₚ π) (sym (inverseʳ π)) (tπ0 ⟨$⟩ʳ i) ⟩
  tπ0 ∘ₚ t0π ∘ₚ π ⟨$⟩ʳ i                                           ≡⟨ cong (π ⟨$⟩ʳ_) (PC.transpose-inverse zero (π ⟨$⟩ˡ zero)) ⟩
  π ⟨$⟩ʳ i                                                         ∎
    where
    tπ0 = transpose (π ⟨$⟩ˡ zero) zero
    t0π = transpose zero (π ⟨$⟩ˡ zero)
