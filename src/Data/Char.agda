------------------------------------------------------------------------
-- The Agda standard library
--
-- Characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char where

open import Data.Nat.Properties using (<-strictTotalOrder)
open import Relation.Binary using (Setoid; StrictTotalOrder)
import Relation.Binary.Construct.On as On
import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Re-export base definitions and decidability of equality

open import Data.Char.Base public
open import Data.Char.Properties using (_≟_) public

------------------------------------------------------------------------
-- Equality over characters

setoid : Setoid _ _
setoid = PropEq.setoid Char

------------------------------------------------------------------------
-- An ordering induced by the toNat function.

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = On.strictTotalOrder <-strictTotalOrder toNat
