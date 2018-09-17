------------------------------------------------------------------------
-- The Agda standard library
--
-- Characters
------------------------------------------------------------------------

module Data.Char where

open import Data.Nat.Properties using (<-strictTotalOrder)
open import Relation.Binary using (Setoid; StrictTotalOrder)
import Relation.Binary.Construction.On as On
import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Re-export base definitions publically

open import Data.Char.Base public

------------------------------------------------------------------------
-- Equality over characters

setoid : Setoid _ _
setoid = PropEq.setoid Char

------------------------------------------------------------------------
-- An ordering induced by the toNat function.

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = On.strictTotalOrder <-strictTotalOrder toNat
