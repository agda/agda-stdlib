------------------------------------------------------------------------
-- The Agda standard library
--
-- The universe polymorphic unit type and the total relation on unit
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit.Polymorphic where

------------------------------------------------------------------------
-- Re-export contents of Base module

open import Data.Unit.Polymorphic.Base public

------------------------------------------------------------------------
-- Re-export query operations

open import Data.Unit.Polymorphic.Properties public using (_≟_)
