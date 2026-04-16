------------------------------------------------------------------------
-- The Agda standard library
--
-- An implementation of merge sort
------------------------------------------------------------------------

-- Unless you are need a particular property of MergeSort, you should
-- import and use the sorting algorithm from `Data.List.Sort` instead
-- of this file.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecTotalOrder)

module Data.List.Sort.MergeSort.Base
  {a ℓ₁ ℓ₂} (O : DecTotalOrder a ℓ₁ ℓ₂) where

open import Data.List.Base
  using (List; []; _∷_; merge; length; map; [_])

open import Data.Nat.Base using (_<_; _>_; z<s; s<s)
open import Data.Nat.Induction
open import Data.Nat.Properties using (m<n⇒m<1+n)

open DecTotalOrder O renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition

mergePairs : List (List A) → List (List A)
mergePairs (xs ∷ ys ∷ yss) = merge _≤?_ xs ys ∷ mergePairs yss
mergePairs xss             = xss

private
  length-mergePairs : ∀ xs ys yss → let zss = xs ∷ ys ∷ yss in
                      length (mergePairs zss) < length zss
  length-mergePairs _ _ []              = s<s z<s
  length-mergePairs _ _ (xs ∷ [])       = s<s (s<s z<s)
  length-mergePairs _ _ (xs ∷ ys ∷ yss) = s<s (m<n⇒m<1+n (length-mergePairs xs ys yss))

mergeAll : (xss : List (List A)) → Acc _<_ (length xss) → List A
mergeAll []        _               = []
mergeAll (xs ∷ []) _               = xs
mergeAll xss@(xs ∷ ys ∷ yss) (acc rec) = mergeAll
  (mergePairs xss) (rec (length-mergePairs xs ys yss))

sort : List A → List A
sort xs = mergeAll (map [_] xs) (<-wellFounded-fast _)
