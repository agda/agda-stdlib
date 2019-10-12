------------------------------------------------------------------------
-- The Agda standard library
--
-- The unit type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit where

open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Re-export contents of base module

open import Data.Unit.Base public

------------------------------------------------------------------------
-- Re-export query operations

open import Data.Unit.Properties public
  using (_≟_)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

setoid = Data.Unit.Properties.≡-setoid
{-# WARNING_ON_USAGE setoid
"Warning: setoid was deprecated in v1.1.
Please use ≡-setoid from Data.Unit.Properties instead."
#-}
decSetoid = Data.Unit.Properties.≡-decSetoid
{-# WARNING_ON_USAGE decSetoid
"Warning: decSetoid was deprecated in v1.1.
Please use ≡-decSetoid from Data.Unit.Properties instead."
#-}
