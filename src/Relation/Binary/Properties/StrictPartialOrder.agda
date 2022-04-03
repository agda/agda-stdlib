------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by strict partial orders
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Properties.StrictPartialOrder
       {s₁ s₂ s₃} (SPO : StrictPartialOrder s₁ s₂ s₃) where

import Relation.Binary.Construct.Converse as Converse
import Relation.Binary.Construct.StrictToNonStrict

open Relation.Binary.StrictPartialOrder SPO

------------------------------------------------------------------------
-- The inverse relation is also a strict partial order.

>-strictPartialOrder : StrictPartialOrder s₁ s₂ s₃
>-strictPartialOrder = Converse.strictPartialOrder SPO

open StrictPartialOrder >-strictPartialOrder public
  using ()
  renaming
  ( _<_                  to _>_
  ; irrefl               to >-irrefl
  ; trans                to >-trans
  ; <-resp-≈             to >-resp-≈
  ; isStrictPartialOrder to >-isStrictPartialOrder
  )

------------------------------------------------------------------------
-- Strict partial orders can be converted to posets

open Relation.Binary.Construct.StrictToNonStrict _≈_ _<_

poset : Poset _ _ _
poset = record
  { isPartialOrder = isPartialOrder isStrictPartialOrder
  }

open Poset poset public
