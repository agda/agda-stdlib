------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- Data.Vec.Relation.Binary.Equality.DecSetoid directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.Vec.Relation.Equality.DecSetoid
  {a ℓ} (DS : DecSetoid a ℓ) where

open import Data.Vec.Relation.Binary.Equality.DecSetoid public
