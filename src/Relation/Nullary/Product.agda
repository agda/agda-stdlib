------------------------------------------------------------------------
-- The Agda standard library
--
-- Products of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Product where

{-# WARNING_ON_IMPORT
"Relation.Nullary.Product was deprecated in v2.0.
Use `Relation.Nullary` instead."
#-}

open import Relation.Nullary.Decidable.Core public using (_×-dec_)
open import Relation.Nullary.Reflects public using (_×-reflects_)
