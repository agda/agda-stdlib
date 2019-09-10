------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by strict partial orders
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Properties.StrictTotalOrder
       {s₁ s₂ s₃} (STO : StrictTotalOrder s₁ s₂ s₃)
       where

open Relation.Binary.StrictTotalOrder STO
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
