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
