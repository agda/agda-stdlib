------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Implication where

{-# WARNING_ON_IMPORT
"Relation.Nullary.Implication was deprecated in v2.0.
Use `Relation.Nullary.Decidable` or `Relation.Nullary` instead."
#-}

open import Relation.Nullary.Decidable.Core public using (_→-dec_)
open import Relation.Nullary.Reflects public using (_→-reflects_)
