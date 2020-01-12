------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- Data.List.Relation.Binary.Equality.DecSetoid directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Equality.DecSetoid
  {a ℓ} (DS : DecSetoid a ℓ) where

open import Data.List.Relation.Binary.Equality.DecSetoid DS public

{-# WARNING_ON_IMPORT
"Data.List.Relation.Equality.DecSetoid was deprecated in v1.0.
Use Data.List.Relation.Binary.Equality.DecSetoid instead."
#-}
