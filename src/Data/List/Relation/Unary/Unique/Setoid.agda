------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists made up entirely of unique elements (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Unary.Unique.Setoid {a ℓ} (S : Setoid a ℓ) where

open Setoid S using (_≉_)

------------------------------------------------------------------------
-- Definition

open import Data.List.Relation.Unary.AllPairs.Core _≉_ public
  renaming (AllPairs to Unique)

open import Data.List.Relation.Unary.AllPairs {R = _≉_} public
  using (head; tail)
