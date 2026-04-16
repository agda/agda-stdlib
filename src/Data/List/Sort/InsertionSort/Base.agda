------------------------------------------------------------------------
-- The Agda standard library
--
-- An implementation of insertion sort
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecTotalOrder)

module Data.List.Sort.InsertionSort.Base
  {a ℓ₁ ℓ₂}
  (O : DecTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Nullary.Decidable.Core using (does)

open DecTotalOrder O renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

insert : A → List A → List A
insert x [] = x ∷ []
insert x (y ∷ xs) = if does (x ≤? y)
  then x ∷ y ∷ xs
  else y ∷ insert x xs

sort : List A → List A
sort [] = []
sort (x ∷ xs) = insert x (sort xs)
