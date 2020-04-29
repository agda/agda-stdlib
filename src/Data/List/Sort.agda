------------------------------------------------------------------------
-- The Agda standard library
--
-- Functions and definitions for sorting lists
------------------------------------------------------------------------

-- See `Data.List.Relation.Unary.Sorted` for the property of a list
-- being sorted.

open import Data.List.Base using (List)
open import Relation.Binary using (DecTotalOrder)

module Data.List.Sort
  {a ℓ₁ ℓ₂} (O : DecTotalOrder a ℓ₁ ℓ₂)
  where

open DecTotalOrder O renaming (Carrier to A)
open import Data.List.Relation.Binary.Permutation.Setoid Eq.setoid
open import Data.List.Relation.Unary.Sorted.TotalOrder totalOrder

------------------------------------------------------------------------
-- Re-export core definitions

open import Data.List.Sort.Base totalOrder public
  using (SortingAlgorithm)

------------------------------------------------------------------------
-- An instance of a sorting algorithm

abstract

  import Data.List.Sort.QuickSort O as Quicksort

  sort : List A → List A
  sort = Quicksort.sort

  sort-↭ : ∀ xs → sort xs ↭ xs
  sort-↭ = Quicksort.sort-↭

  sort-↗ : ∀ xs → Sorted (sort xs)
  sort-↗ = Quicksort.sort-↗

sortingAlgorithm : SortingAlgorithm
sortingAlgorithm = record
  { sort   = sort
  ; sort-↭ = sort-↭
  ; sort-↗ = sort-↗
  }
