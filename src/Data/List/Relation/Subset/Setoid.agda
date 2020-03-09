------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- Data.List.Relation.Binary.Subset.Setoid directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Subset.Setoid
  {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Relation.Binary.Subset.Setoid S public

{-# WARNING_ON_IMPORT
"Data.List.Relation.Subset.Setoid was deprecated in v1.0.
Use Data.List.Relation.Binary.Subset.Setoid instead."
#-}
