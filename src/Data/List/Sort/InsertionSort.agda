------------------------------------------------------------------------
-- The Agda standard library
--
-- An implementation of insertion sort and its properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecTotalOrder)

module Data.List.Sort.InsertionSort
  {a ℓ₁ ℓ₂}
  (O : DecTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.List.Sort.InsertionSort.Base O public
open import Data.List.Sort.InsertionSort.Properties O using (insertionSort) public
