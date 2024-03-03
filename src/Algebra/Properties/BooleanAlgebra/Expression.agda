------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Lattice

module Algebra.Properties.BooleanAlgebra.Expression
  {b} (B : BooleanAlgebra b b)
  where

{-# WARNING_ON_IMPORT
"Algebra.Properties.BooleanAlgebra.Expression was deprecated in v2.0.
Use Algebra.Lattice.Properties.BooleanAlgebra.Expression instead."
#-}

open import Algebra.Lattice.Properties.BooleanAlgebra.Expression
