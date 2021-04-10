------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists made up entirely of unique elements (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid)
open import Relation.Nullary using (¬_)

module Data.List.Relation.Unary.Unique.Setoid {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition

private
  Distinct : Rel A ℓ
  Distinct x y = ¬ (x ≈ y)

open import Data.List.Relation.Unary.AllPairs.Core Distinct public
  renaming (AllPairs to Unique)

open import Data.List.Relation.Unary.AllPairs {R = Distinct} public
  using (head; tail)

