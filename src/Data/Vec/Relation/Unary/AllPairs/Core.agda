------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors where every pair of elements are related (symmetrically)
------------------------------------------------------------------------

-- Core modules are not meant to be used directly outside of the
-- standard library.

-- This module should be removable if and when Agda issue
-- https://github.com/agda/agda/issues/3210 is fixed

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)

module Data.Vec.Relation.Unary.AllPairs.Core
  {a ℓ} {A : Set a} (R : Rel A ℓ) where

open import Level
open import Data.Vec.Base
open import Data.Vec.Relation.Unary.All

------------------------------------------------------------------------
-- Definition

-- AllPairs R xs means that every pair of elements (x , y) in xs is a
-- member of relation R (as long as x comes before y in the vector).

infixr 5 _∷_

data AllPairs : ∀ {n} → Vec A n → Set (a ⊔ ℓ) where
  []  : AllPairs []
  _∷_ : ∀ {n x} {xs : Vec A n} → All (R x) xs → AllPairs xs → AllPairs (x ∷ xs)
