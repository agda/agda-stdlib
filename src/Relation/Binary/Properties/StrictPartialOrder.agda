------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by strict partial orders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Properties.StrictPartialOrder
       {s₁ s₂ s₃} (SPO : StrictPartialOrder s₁ s₂ s₃) where

open Relation.Binary.StrictPartialOrder SPO
  renaming (trans to <-trans)
open import Relation.Binary.Construct.StrictToNonStrict _≈_ _<_

------------------------------------------------------------------------
-- Strict partial orders can be converted to posets

poset : Poset _ _ _
poset = record
  { isPartialOrder = isPartialOrder isStrictPartialOrder
  }

open Poset poset public
