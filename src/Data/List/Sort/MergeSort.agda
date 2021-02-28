------------------------------------------------------------------------
-- The Agda standard library
--
-- An implementation of merge sort along with proofs of correctness.
------------------------------------------------------------------------

-- Unless you are need a particular property of MergeSort, you should
-- import and use the sorting algorithm from `Data.List.Sort` instead
-- of this file.

{-# OPTIONS --without-K --safe #-}

open import Data.Bool using (true; false)
open import Data.List.Base
open import Data.List.Properties using (length-partition; ++-assoc; concat-[-])
open import Data.List.Relation.Unary.Linked using ([]; [-])
import Data.List.Relation.Unary.Sorted.TotalOrder.Properties as Sorted
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Binary.Permutation.Propositional
import Data.List.Relation.Binary.Permutation.Propositional.Properties as Perm
open import Data.Maybe.Base using (just)
open import Relation.Nullary using (does)
open import Data.Nat using (_<_; _>_; z≤n; s≤s)
open import Data.Nat.Induction
open import Data.Nat.Properties using (≤-step)
open import Data.Product as Prod using (_,_)
open import Function.Base using (_∘_)
open import Relation.Binary using (DecTotalOrder)
open import Relation.Nullary using (¬_)

module Data.List.Sort.MergeSort
  {a ℓ₁ ℓ₂} (O : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder O renaming (Carrier to A)

open import Data.List.Sort.Base totalOrder
open import Data.List.Relation.Unary.Sorted.TotalOrder totalOrder hiding (head)
open import Relation.Binary.Properties.DecTotalOrder O using (_≰_; ≰⇒≥; ≰-respˡ-≈)

open PermutationReasoning

------------------------------------------------------------------------
-- Definition

mergePairs : List (List A) → List (List A)
mergePairs (xs ∷ ys ∷ xss) = merge _≤?_ xs ys ∷ mergePairs xss
mergePairs xss             = xss

private
  length-mergePairs : ∀ xs ys xss → length (mergePairs (xs ∷ ys ∷ xss)) < length (xs ∷ ys ∷ xss)
  length-mergePairs _ _ []              = s≤s (s≤s z≤n)
  length-mergePairs _ _ (xss ∷ [])      = s≤s (s≤s (s≤s z≤n))
  length-mergePairs _ _ (xs ∷ ys ∷ xss) = s≤s (≤-step (length-mergePairs xs ys xss))

mergeAll : (xss : List (List A)) → Acc _<_ (length xss) → List A
mergeAll []        _               = []
mergeAll (xs ∷ []) _               = xs
mergeAll (xs ∷ ys ∷ xss) (acc rec) = mergeAll
  (mergePairs (xs ∷ ys ∷ xss)) (rec _ (length-mergePairs xs ys xss))

sort : List A → List A
sort xs = mergeAll (map [_] xs) (<-wellFounded-fast _)

------------------------------------------------------------------------
-- Permutation property

mergePairs-↭ : ∀ xss → concat (mergePairs xss) ↭ concat xss
mergePairs-↭ []              = ↭-refl
mergePairs-↭ (xs ∷ [])       = ↭-refl
mergePairs-↭ (xs ∷ ys ∷ xss) = begin
  merge _ xs ys ++ concat (mergePairs xss) ↭⟨ Perm.++⁺ (Perm.merge-↭ _ xs ys) (mergePairs-↭ xss) ⟩
  (xs ++ ys)    ++ concat xss              ≡⟨ ++-assoc xs ys (concat xss) ⟩
  xs ++ ys      ++ concat xss              ∎

mergeAll-↭ : ∀ xss (rec : Acc _<_ (length xss)) → mergeAll xss rec ↭ concat xss
mergeAll-↭ []              _ = ↭-refl
mergeAll-↭ (xs ∷ [])       _ = ↭-sym (Perm.++-identityʳ xs)
mergeAll-↭ (xs ∷ ys ∷ xss) (acc rec) = begin
  mergeAll (mergePairs (xs ∷ ys ∷ xss)) _ ↭⟨ mergeAll-↭ (mergePairs (xs ∷ ys ∷ xss)) _ ⟩
  concat   (mergePairs (xs ∷ ys ∷ xss))   ↭⟨ mergePairs-↭ (xs ∷ ys ∷ xss) ⟩
  concat   (xs ∷ ys ∷ xss)                ∎

sort-↭ : ∀ xs → sort xs ↭ xs
sort-↭ xs = begin
  mergeAll (map [_] xs) _ ↭⟨ mergeAll-↭ (map [_] xs) _ ⟩
  concat (map [_] xs)     ≡⟨ concat-[-] xs ⟩
  xs                      ∎

------------------------------------------------------------------------
-- Sorted property

mergePairs-↗ : ∀ {xss} → All Sorted xss → All Sorted (mergePairs xss)
mergePairs-↗ []                 = []
mergePairs-↗ (xs↗ ∷ [])         = xs↗ ∷ []
mergePairs-↗ (xs↗ ∷ ys↗ ∷ xss↗) = Sorted.merge⁺ O xs↗ ys↗ ∷ mergePairs-↗ xss↗

mergeAll-↗ : ∀ {xss} (rec : Acc _<_ (length xss)) →
             All Sorted xss → Sorted (mergeAll xss rec)
mergeAll-↗ rec       []                 = []
mergeAll-↗ rec       (xs↗ ∷ [])         = xs↗
mergeAll-↗ (acc rec) (xs↗ ∷ ys↗ ∷ xss↗) = mergeAll-↗ _ (mergePairs-↗ (xs↗ ∷ ys↗ ∷ xss↗))

sort-↗ : ∀ xs → Sorted (sort xs)
sort-↗ xs = mergeAll-↗ _ (All.map⁺ (All.universal (λ _ → [-]) xs))

------------------------------------------------------------------------
-- Algorithm

mergeSort : SortingAlgorithm
mergeSort = record
  { sort   = sort
  ; sort-↭ = sort-↭
  ; sort-↗ = sort-↗
  }

