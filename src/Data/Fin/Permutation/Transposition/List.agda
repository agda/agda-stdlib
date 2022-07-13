------------------------------------------------------------------------
-- The Agda standard library
--
-- Decomposition of permutations into a list of transpositions.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Permutation.Transposition.List where

open import Data.Fin.Base
open import Data.Fin.Patterns using (0F)
open import Data.Fin.Permutation as P hiding (lift₀)
open import Data.Fin.Properties using (_≟_; suc-injective)
import Data.Fin.Permutation.Components as PC
open import Data.List as L using (List; []; _∷_; _++_; map)
import Data.List.Properties as L
open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Product using (∃₂; _×_; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; module ≡-Reasoning)
open ≡-Reasoning

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Definition

-- This decomposition is not a unique representation of the original
-- permutation but can be used to simply proofs about permutations (by
-- instead inducting on the list of transpositions, where a
-- transposition is a permutation swapping two distinct elements and
-- leaving the rest in place).

TranspositionList : ℕ → Set
TranspositionList n = List (∃₂ λ (i j : Fin n) → i ≢ j)

------------------------------------------------------------------------
-- Operations on transposition lists

lift₀ : TranspositionList n → TranspositionList (suc n)
lift₀ xs = map (λ (i , j , i≢j) → (suc i , suc j , i≢j ∘ suc-injective)) xs

eval : TranspositionList n → Permutation′ n
eval []             = id
eval ((i , j , _) ∷ xs) = transpose i j ∘ₚ eval xs

decompose : Permutation′ n → TranspositionList n
decompose {zero}  π = []
decompose {suc n} π with π ⟨$⟩ˡ 0F
... | 0F = lift₀ (decompose (remove 0F π))
... | x@(suc _) = (x , 0F , λ ()) ∷ lift₀ (decompose (remove 0F ((transpose 0F (π ⟨$⟩ˡ 0F)) ∘ₚ π)))

------------------------------------------------------------------------
-- Properties

eval-lift : ∀ (xs : TranspositionList n) → eval (lift₀ xs) ≈ P.lift₀ (eval xs)
eval-lift []               = sym ∘ lift₀-id
eval-lift ((i , j , _) ∷ xs) k = begin
  transpose (suc i) (suc j) ∘ₚ eval (lift₀ xs) ⟨$⟩ʳ k     ≡⟨ cong (eval (lift₀ xs) ⟨$⟩ʳ_) (lift₀-transpose i j k) ⟩
  P.lift₀ (transpose i j) ∘ₚ eval (lift₀ xs) ⟨$⟩ʳ k       ≡⟨ eval-lift xs (P.lift₀ (transpose i j) ⟨$⟩ʳ k) ⟩
  P.lift₀ (eval xs) ⟨$⟩ʳ (P.lift₀ (transpose i j) ⟨$⟩ʳ k) ≡⟨ lift₀-comp (transpose i j) (eval xs) k ⟩
  P.lift₀ (transpose i j ∘ₚ eval xs) ⟨$⟩ʳ k               ∎

eval-decompose : ∀ (π : Permutation′ n) → eval (decompose π) ≈ π
eval-decompose {suc n} π i with π ⟨$⟩ˡ 0F in p
... | 0F = begin
  eval (lift₀ (decompose (remove 0F π)))   ⟨$⟩ʳ i ≡⟨ eval-lift (decompose (remove 0F π)) i ⟩
  P.lift₀ (eval (decompose (remove 0F π))) ⟨$⟩ʳ i ≡⟨ lift₀-cong _ _ (eval-decompose (remove 0F π)) i ⟩
  P.lift₀ (remove 0F π)                    ⟨$⟩ʳ i ≡⟨ lift₀-remove π (trans (cong (π ⟨$⟩ʳ_) (sym p)) (P.inverseʳ π)) i ⟩
  π                                        ⟨$⟩ʳ i ∎
... | x@(suc _) = begin
  tx0 ∘ₚ eval (lift₀ (decompose (remove 0F (t0π ∘ₚ π))))   ⟨$⟩ʳ i ≡⟨ eval-lift (decompose (remove 0F (t0π ∘ₚ π))) (tx0 ⟨$⟩ʳ i) ⟩
  tx0 ∘ₚ P.lift₀ (eval (decompose (remove 0F (t0π ∘ₚ π)))) ⟨$⟩ʳ i ≡⟨ lift₀-cong _ _ (eval-decompose _) (tx0 ⟨$⟩ʳ i) ⟩
  tx0 ∘ₚ P.lift₀ (remove 0F (t0π ∘ₚ π))                    ⟨$⟩ʳ i ≡⟨ lift₀-remove (t0π ∘ₚ π) (inverseʳ π) (tx0 ⟨$⟩ʳ i) ⟩
  tx0 ∘ₚ t0π ∘ₚ π                                          ⟨$⟩ʳ i ≡⟨ cong (λ x′ → tx0 ∘ₚ transpose 0F x′ ∘ₚ π ⟨$⟩ʳ i) p ⟩
  tx0 ∘ₚ transpose 0F x ∘ₚ π                               ⟨$⟩ʳ i ≡⟨ cong (π ⟨$⟩ʳ_) (PC.transpose-inverse 0F x) ⟩
  π                                                       ⟨$⟩ʳ i ∎
    where
      tx0 = transpose x 0F
      t0π = transpose 0F (π ⟨$⟩ˡ 0F)

eval-++ : ∀ (xs ys : TranspositionList n) → eval (xs ++ ys) ≈ eval xs ∘ₚ eval ys
eval-++ [] ys i = refl
eval-++ ((a , b , _) ∷ xs) ys i = eval-++ xs ys (transpose a b ⟨$⟩ʳ i)

eval-reverse : ∀ (xs : TranspositionList n) → eval (L.reverse xs) ≈ flip (eval xs)
eval-reverse [] i = refl
eval-reverse (x@(a , b , _) ∷ xs) i = begin
  eval (L.reverse (x ∷ xs))            ⟨$⟩ʳ i ≡⟨ cong (λ p → eval p ⟨$⟩ʳ i) (L.unfold-reverse x xs) ⟩
  eval (L.reverse xs L.∷ʳ x)           ⟨$⟩ʳ i ≡⟨ eval-++ (L.reverse xs) L.[ x ] i ⟩
  eval (L.reverse xs) ∘ₚ transpose a b ⟨$⟩ʳ i ≡⟨ cong (transpose a b ⟨$⟩ʳ_) (eval-reverse xs i) ⟩
  flip (eval xs) ∘ₚ transpose a b      ⟨$⟩ʳ i ≡⟨ transpose-self-inverse a b (flip (eval xs) ⟨$⟩ʳ i) ⟩
  flip (eval xs) ∘ₚ transpose b a      ⟨$⟩ʳ i ∎

