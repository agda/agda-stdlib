------------------------------------------------------------------------
-- The Agda standard library
--
-- Notation for freely adding an infimum to any set
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Construct.Add.Infimum where

open import Relation.Nullary.Construct.Add.Point public
  renaming (Pointed to _₋; ∙ to ⊥₋)

