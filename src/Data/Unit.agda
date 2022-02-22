------------------------------------------------------------------------
-- The Agda standard library
--
-- The unit type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit where

import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Re-export contents of base module

open import Data.Unit.Base public

------------------------------------------------------------------------
-- Re-export query operations

open import Data.Unit.Properties public
  using (_≟_)
