------------------------------------------------------------------------
-- The Agda standard library
--
-- Solver for equations in idempotent commutative monoids
--
-- Adapted from Algebra.Solver.CommutativeMonoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (IdempotentCommutativeMonoid)

module Algebra.Solver.IdempotentCommutativeMonoid
  {c ℓ} (M : IdempotentCommutativeMonoid c ℓ) where

import Algebra.Solver.IdempotentCommutativeMonoid.Normal as Normal
import Algebra.Solver.Monoid.Tactic as Tactic

open IdempotentCommutativeMonoid M using (monoid)

------------------------------------------------------------------------
-- Normal forms

open module N = Normal M public
  renaming (correct to normalise-correct)

------------------------------------------------------------------------
-- Tactic

open Tactic monoid (record { N }) public


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.2

{-# WARNING_ON_USAGE normalise-correct
"Warning: normalise-correct was deprecated in v2.2.
Please use Algebra.Solver.IdempotentCommutativeMonoid.Normal.correct instead."
#-}
