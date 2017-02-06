------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

module Data.String where

open import Data.List.Base as List using (_∷_; []; List)
open import Data.Vec as Vec using (Vec)
open import Data.Colist as Colist using (Colist)
open import Data.Char as Char using (Char)
open import Function
open import Relation.Binary
open import Relation.Binary.List.StrictLex as StrictLex
import Relation.Binary.On as On
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

open import Data.String.Base public

-- Possibly infinite strings.

Costring : Set
Costring = Colist Char

------------------------------------------------------------------------
-- Operations

toVec : (s : String) → Vec Char (List.length (toList s))
toVec = Vec.fromList ∘ toList

toCostring : String → Costring
toCostring = Colist.fromList ∘ toList

setoid : Setoid _ _
setoid = PropEq.setoid String

-- Lexicographic ordering of strings.

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder =
  On.strictTotalOrder
    (StrictLex.<-strictTotalOrder Char.strictTotalOrder)
    toList
