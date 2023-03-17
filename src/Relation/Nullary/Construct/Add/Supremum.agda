------------------------------------------------------------------------
-- The Agda standard library
--
-- Notation for freely adding a supremum to any set
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Construct.Add.Supremum where

open import Relation.Nullary.Construct.Add.Point
  renaming (Pointed to _⁺; ∙ to ⊤⁺)
  public
