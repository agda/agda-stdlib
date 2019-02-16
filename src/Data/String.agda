------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String where

open import Data.Vec as Vec using (Vec)
open import Data.Char as Char using (Char)
open import Data.List.Relation.Binary.Lex.Strict as StrictLex
open import Relation.Binary using (Setoid; StrictTotalOrder)
import Relation.Binary.Construct.On as On
import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Re-export contents of base publically

open import Data.String.Base public

------------------------------------------------------------------------
-- Operations

toVec : (s : String) → Vec Char (length s)
toVec s = Vec.fromList (toList s)

------------------------------------------------------------------------
-- Equality over strings

setoid : Setoid _ _
setoid = PropEq.setoid String

------------------------------------------------------------------------
-- A lexicographic ordering on strings.

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder =
  On.strictTotalOrder
    (StrictLex.<-strictTotalOrder Char.strictTotalOrder)
    toList
