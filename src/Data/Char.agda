------------------------------------------------------------------------
-- The Agda standard library
--
-- Characters
------------------------------------------------------------------------

module Data.Char where

import Data.Nat.Properties as NatProp

open import Relation.Binary
import Relation.Binary.On as On
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

open import Data.Char.Base
open        Data.Char.Base public using (Char; show; toNat)

-- Informative equality test.

setoid : Setoid _ _
setoid = PropEq.setoid Char

-- An ordering induced by the toNat function.

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = On.strictTotalOrder NatProp.strictTotalOrder toNat
