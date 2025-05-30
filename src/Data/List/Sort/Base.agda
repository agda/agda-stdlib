------------------------------------------------------------------------
-- The Agda standard library
--
-- The core definition of a sorting algorithm
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (TotalOrder)

module Data.List.Sort.Base
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂)
  where

open import Data.List.Base using (List)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Level using (_⊔_)

open TotalOrder totalOrder renaming (Carrier to A)
open import Data.List.Relation.Unary.Sorted.TotalOrder totalOrder

------------------------------------------------------------------------
-- Definition of a sorting algorithm

record SortingAlgorithm : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    sort   : List A → List A

    -- The output of `sort` is a permutation of the input
    sort-↭ : ∀ xs → sort xs ↭ xs

    -- The output of `sort` is sorted.
    sort-↗ : ∀ xs → Sorted (sort xs)
