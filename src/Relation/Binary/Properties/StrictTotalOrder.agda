------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by strict partial orders
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder; DecTotalOrder)

module Relation.Binary.Properties.StrictTotalOrder
       {s₁ s₂ s₃} (STO : StrictTotalOrder s₁ s₂ s₃)
       where

-- issue #1214: locally to this module, we hide the relation _≮_, so
-- that we can deprecate its export here, yet re-export it elsewhere
open StrictTotalOrder STO hiding (_≮_)
open import Relation.Binary.Construct.StrictToNonStrict _≈_ _<_
import Relation.Binary.Properties.StrictPartialOrder as SPO
open import Relation.Binary.Consequences

------------------------------------------------------------------------
-- _<_ - the strict version is a strict total order

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { isDecTotalOrder = isDecTotalOrder isStrictTotalOrder
  }

open DecTotalOrder decTotalOrder public

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

-- issue #1214: see above
infix 4 _≮_
_≮_ = StrictTotalOrder._≮_ STO
{-# WARNING_ON_USAGE _≮_
"Warning: export of _≮_ from this module was deprecated in v2.0. Please import from Relation.Binary.Bundles.StrictPartialOrder._≮_ instead"
#-}
