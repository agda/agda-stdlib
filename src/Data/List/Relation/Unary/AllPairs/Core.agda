------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where every pair of elements are related (symmetrically)
------------------------------------------------------------------------

-- Core modules are not meant to be used directly outside of the
-- standard library.

-- This module should be removable if and when Agda issue
-- https://github.com/agda/agda/issues/3210 is fixed

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)

module Data.List.Relation.Unary.AllPairs.Core
       {a ℓ} {A : Set a} (R : Rel A ℓ) where

open import Level
open import Data.List.Base
open import Data.List.Relation.Unary.All

------------------------------------------------------------------------
-- Definition

-- AllPairs R xs means that every pair of elements (x , y) in xs is a
-- member of relation R (as long as x comes before y in the list).

infixr 5 _∷_

data AllPairs : List A → Set (a ⊔ ℓ) where
  []  : AllPairs []
  _∷_ : ∀ {x xs} → All (R x) xs → AllPairs xs → AllPairs (x ∷ xs)
