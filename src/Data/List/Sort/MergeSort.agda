------------------------------------------------------------------------
-- The Agda standard library
--
-- An implementation of merge sort along with proofs of correctness.
------------------------------------------------------------------------

-- Unless you are need a particular property of MergeSort, you should
-- import and use the sorting algorithm from `Data.List.Sort` instead
-- of this file.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecTotalOrder)

module Data.List.Sort.MergeSort
  {a ℓ₁ ℓ₂} (O : DecTotalOrder a ℓ₁ ℓ₂) where

open import Data.List.Sort.MergeSort.Base O public
open import Data.List.Sort.MergeSort.Properties O using (mergeSort) public
