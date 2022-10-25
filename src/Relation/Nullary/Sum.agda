------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Sum where

{-# WARNING_ON_IMPORT
"Relation.Nullary.Sum was deprecated in v2.0.
Use `Relation.Nullary` instead."
#-}

open import Relation.Nullary.Negation.Core public using (_¬-⊎_)
open import Relation.Nullary.Reflects public using (_⊎-reflects_)
open import Relation.Nullary.Decidable.Core public using (_⊎-dec_)
