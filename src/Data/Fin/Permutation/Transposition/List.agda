------------------------------------------------------------------------
-- The Agda standard library
--
-- Decomposition of permutations into a list of transpositions.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Permutation.Transposition.List where

open import Data.Fin.Base
open import Data.Fin.Patterns using (0F)
open import Data.Fin.Permutation as P hiding (lift₀)
import Data.Fin.Permutation.Components as PC
open import Data.List using (List; []; _∷_; map)
open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; cong; module ≡-Reasoning)
open ≡-Reasoning

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Definition

-- This decomposition is not a unique representation of the original
-- permutation but can be used to simply proofs about permutations (by
-- instead inducting on the list of transpositions).

TranspositionList : ℕ → Set
TranspositionList n = List (Fin n × Fin n)

------------------------------------------------------------------------
-- Operations on transposition lists

lift₀ : TranspositionList n → TranspositionList (suc n)
lift₀ xs = map (λ (i , j) → (suc i , suc j)) xs

eval : TranspositionList n → Permutation′ n
eval []             = id
eval ((i , j) ∷ xs) = transpose i j ∘ₚ eval xs

decompose : Permutation′ n → TranspositionList n
decompose {zero}  π = []
decompose {suc n} π = (π ⟨$⟩ˡ 0F , 0F) ∷ lift₀ (decompose (remove 0F ((transpose 0F (π ⟨$⟩ˡ 0F)) ∘ₚ π)))

------------------------------------------------------------------------
-- Properties

eval-lift : ∀ (xs : TranspositionList n) → eval (lift₀ xs) ≈ P.lift₀ (eval xs)
eval-lift []               = sym ∘ lift₀-id
eval-lift ((i , j) ∷ xs) k = begin
  transpose (suc i) (suc j) ∘ₚ eval (lift₀ xs) ⟨$⟩ʳ k     ≡⟨ cong (eval (lift₀ xs) ⟨$⟩ʳ_) (lift₀-transpose i j k) ⟩
  P.lift₀ (transpose i j) ∘ₚ eval (lift₀ xs) ⟨$⟩ʳ k       ≡⟨ eval-lift xs (P.lift₀ (transpose i j) ⟨$⟩ʳ k) ⟩
  P.lift₀ (eval xs) ⟨$⟩ʳ (P.lift₀ (transpose i j) ⟨$⟩ʳ k) ≡⟨ lift₀-comp (transpose i j) (eval xs) k ⟩
  P.lift₀ (transpose i j ∘ₚ eval xs) ⟨$⟩ʳ k               ∎

eval-decompose : ∀ (π : Permutation′ n) → eval (decompose π) ≈ π
eval-decompose {suc n} π i = begin
  tπ0 ∘ₚ eval (lift₀ (decompose (remove 0F (t0π ∘ₚ π))))   ⟨$⟩ʳ i ≡⟨ eval-lift (decompose (remove 0F (t0π ∘ₚ π))) (tπ0 ⟨$⟩ʳ i) ⟩
  tπ0 ∘ₚ P.lift₀ (eval (decompose (remove 0F (t0π ∘ₚ π)))) ⟨$⟩ʳ i ≡⟨ lift₀-cong _ _ (eval-decompose _) (tπ0 ⟨$⟩ʳ i) ⟩
  tπ0 ∘ₚ P.lift₀ (remove 0F (t0π ∘ₚ π))                    ⟨$⟩ʳ i ≡⟨ lift₀-remove (t0π ∘ₚ π) (inverseʳ π) (tπ0 ⟨$⟩ʳ i) ⟩
  tπ0 ∘ₚ t0π ∘ₚ π                                          ⟨$⟩ʳ i ≡⟨ cong (π ⟨$⟩ʳ_) (PC.transpose-inverse 0F (π ⟨$⟩ˡ 0F)) ⟩
  π                                                        ⟨$⟩ʳ i ∎
  where
  tπ0 = transpose (π ⟨$⟩ˡ 0F) 0F
  t0π = transpose 0F (π ⟨$⟩ˡ 0F)
