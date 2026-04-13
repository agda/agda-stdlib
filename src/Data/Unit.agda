------------------------------------------------------------------------
-- The Agda standard library
--
-- The unit type, Level-monomorphic version
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit where

------------------------------------------------------------------------
-- Re-export contents of base module

open import Data.Unit.Base public

------------------------------------------------------------------------
-- Re-export query operations

open import Data.Unit.Properties public
  using (_≟_)
