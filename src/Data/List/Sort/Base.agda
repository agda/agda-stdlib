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
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭⇒↭ₛ)
import Data.List.Relation.Binary.Permutation.Homogeneous as Homo
open import Level using (_⊔_)

open TotalOrder totalOrder renaming (Carrier to A)
open import Data.List.Relation.Unary.Sorted.TotalOrder totalOrder
import Data.List.Relation.Binary.Permutation.Setoid Eq.setoid as S

------------------------------------------------------------------------
-- Definition of a sorting algorithm

record SortingAlgorithm : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    sort   : List A → List A

    -- The output of `sort` is a propositional permutation of the input.
    -- Note that the choice of using a propositional equality here
    -- is very deliberate. A sorting algorithm should only be capable
    -- of altering the order of the elements of the list, and should not
    -- be capable of altering the elements themselves in any way.
    sort-↭ : ∀ xs → sort xs ↭ xs

    -- The output of `sort` is sorted.
    sort-↗ : ∀ xs → Sorted (sort xs)

  -- Lists are also permutations under the setoid versions of
  -- permutation.
  sort-↭ₛ : ∀ xs → sort xs S.↭ xs
  sort-↭ₛ xs = Homo.map Eq.reflexive (↭⇒↭ₛ (sort-↭ xs))
