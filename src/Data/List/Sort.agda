------------------------------------------------------------------------
-- The Agda standard library
--
-- Functions and definitions for sorting lists
------------------------------------------------------------------------

-- See `Data.List.Relation.Unary.Sorted` for the property of a list
-- being sorted.

{-# OPTIONS --without-K --safe #-}

open import Data.List.Base using (List)
open import Relation.Binary using (DecTotalOrder)

module Data.List.Sort
  {a ℓ₁ ℓ₂} (O : DecTotalOrder a ℓ₁ ℓ₂)
  where

open DecTotalOrder O renaming (Carrier to A)

------------------------------------------------------------------------
-- Re-export core definitions

open import Data.List.Sort.Base totalOrder public
  using (SortingAlgorithm)

------------------------------------------------------------------------
-- An instance of a sorting algorithm

open import Data.List.Sort.MergeSort O using (mergeSort)

abstract
  sortingAlgorithm : SortingAlgorithm
  sortingAlgorithm = mergeSort

open SortingAlgorithm sortingAlgorithm public
  using
  ( sort   -- : List A → List A
  ; sort-↭ -- : ∀ xs → sort xs ↭ xs
  ; sort-↗ -- : ∀ xs → Sorted (sort xs)
  )
