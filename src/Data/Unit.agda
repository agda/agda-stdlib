------------------------------------------------------------------------
-- The Agda standard library
--
-- The unit type
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Unit where

------------------------------------------------------------------------
-- Re-export contents of base module

open import Data.Unit.Base public

------------------------------------------------------------------------
-- Re-export query operations

open import Data.Unit.Properties public
  using (_≟_)
