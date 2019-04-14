------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- Data.List.Relation.Binary.Equality.Setoid directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Equality.Setoid {a ℓ} (S : Setoid a ℓ) where

open import Data.List.Relation.Binary.Equality.Setoid S public

{-# WARNING_ON_IMPORT
"Data.List.Relation.Equality.Setoid was deprecated in v1.0.
Use Data.List.Relation.Binary.Equality.Setoid instead."
#-}
