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

open StrictTotalOrder STO
open import Relation.Binary.Construct.StrictToNonStrict _≈_ _<_
import Relation.Binary.Properties.StrictPartialOrder as SPO
open import Relation.Binary.Consequences

------------------------------------------------------------------------
-- _<_ - the strict version is a decidable total order

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { isDecTotalOrder = isDecTotalOrder isStrictTotalOrder
  }

open DecTotalOrder decTotalOrder public
