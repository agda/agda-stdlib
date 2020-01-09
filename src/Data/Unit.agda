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
  using (_≟_; _≤?_)

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
total = Data.Unit.Properties.≤-total
{-# WARNING_ON_USAGE total
"Warning: total was deprecated in v1.1.
Please use ≤-total from Data.Unit.Properties instead."
#-}
poset = Data.Unit.Properties.≤-poset
{-# WARNING_ON_USAGE poset
"Warning: poset was deprecated in v1.1.
Please use ≤-poset from Data.Unit.Properties instead."
#-}
decTotalOrder = Data.Unit.Properties.≤-decTotalOrder
{-# WARNING_ON_USAGE decTotalOrder
"Warning: decTotalOrder was deprecated in v1.1.
Please use ≤-decTotalOrder from Data.Unit.Properties instead."
#-}
preorder = PropEq.preorder ⊤
{-# WARNING_ON_USAGE decTotalOrder
"Warning: preorder was deprecated in v1.1."
#-}
