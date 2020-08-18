------------------------------------------------------------------------
-- The Agda standard library
--
-- Decomposition of permutations into a list of transpositions.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Permutation.Transposition.List where

open import Data.Fin.Base
open import Data.Fin.Patterns
open import Data.Fin.Permutation renaming (lift₀ to lift₀′)
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

eval : ∀ {n} → TranspositionList n → Permutation′ n
eval L.[] = id
eval ((i , j) L.∷ xs) = (transpose i j) ∘ₚ (eval xs)

lift₀ : ∀ {n} → TranspositionList n → TranspositionList (suc n)
lift₀ xs = L.map (λ (i , j) → (suc i , suc j)) xs

------------------------------------------------------------------------
-- Decomposition of a permutation into transpositions

-- This decomposition is not a unique representation of the original
-- permutation but can be used to simply proofs about permutations (by
-- instead inducting on the list of transpositions).

decompose : ∀ {n} → Permutation′ n → TranspositionList n
decompose {zero} π = L.[]
decompose {suc n} π = (π ⟨$⟩ˡ 0F , 0F) L.∷ lift₀ (decompose (remove 0F ((transpose 0F (π ⟨$⟩ˡ 0F)) ∘ₚ π)))

------------------------------------------------------------------------
-- Properties

eval-lift : ∀ {n} (xs : TranspositionList n) i → eval (lift₀ xs) ⟨$⟩ʳ i ≡ lift₀′ (eval xs) ⟨$⟩ʳ i
eval-lift L.[] = sym ∘ lift₀-id
eval-lift ((i , j) L.∷ xs) k = begin
  transpose (suc i) (suc j) ∘ₚ eval (lift₀ xs) ⟨$⟩ʳ k   ≡⟨ cong (eval (lift₀ xs) ⟨$⟩ʳ_) (lift₀-transpose i j k) ⟩
  lift₀′ (transpose i j) ∘ₚ eval (lift₀ xs) ⟨$⟩ʳ k      ≡⟨ eval-lift xs (lift₀′ (transpose i j) ⟨$⟩ʳ k) ⟩
  lift₀′ (eval xs) ⟨$⟩ʳ (lift₀′ (transpose i j) ⟨$⟩ʳ k) ≡⟨ lift₀-comp (transpose i j) (eval xs) k ⟩
  lift₀′ (transpose i j ∘ₚ eval xs) ⟨$⟩ʳ k              ∎

eval-decompose : ∀ {n} (π : Permutation′ n) i → eval (decompose π) ⟨$⟩ʳ i ≡ π ⟨$⟩ʳ i
eval-decompose {zero} π ()
eval-decompose {suc n} π i = begin
  tπ0 ∘ₚ eval (lift₀ (decompose (remove 0F (t0π ∘ₚ π)))) ⟨$⟩ʳ i  ≡⟨ eval-lift (decompose (remove 0F (t0π ∘ₚ π))) (tπ0 ⟨$⟩ʳ i) ⟩
  tπ0 ∘ₚ lift₀′ (eval (decompose (remove 0F (t0π ∘ₚ π)))) ⟨$⟩ʳ i ≡⟨ lift₀-cong _ _ (eval-decompose _) (tπ0 ⟨$⟩ʳ i) ⟩
  tπ0 ∘ₚ lift₀′ (remove 0F (t0π ∘ₚ π)) ⟨$⟩ʳ i                    ≡⟨ lift₀-remove (t0π ∘ₚ π) (sym (inverseʳ π)) (tπ0 ⟨$⟩ʳ i) ⟩
  tπ0 ∘ₚ t0π ∘ₚ π ⟨$⟩ʳ i                                         ≡⟨ cong (π ⟨$⟩ʳ_) (PC.transpose-inverse 0F (π ⟨$⟩ˡ 0F)) ⟩
  π ⟨$⟩ʳ i                                                       ∎
    where
    tπ0 = transpose (π ⟨$⟩ˡ 0F) 0F
    t0π = transpose 0F (π ⟨$⟩ˡ 0F)
