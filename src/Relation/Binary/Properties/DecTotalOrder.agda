------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by decidable total orders
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Relation.Binary

module Relation.Binary.Properties.DecTotalOrder
         {d₁ d₂ d₃} (DT : DecTotalOrder d₁ d₂ d₃) where

open Relation.Binary.DecTotalOrder DT hiding (trans)
open import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder₂ isDecTotalOrder
  }

open StrictTotalOrder strictTotalOrder public
