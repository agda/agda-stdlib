------------------------------------------------------------------------
-- The Agda standard library
--
-- Solver for equations in commutative monoids
--
-- Adapted from Algebra.Solver.Monoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)

module Algebra.Solver.CommutativeMonoid {c ℓ} (M : CommutativeMonoid c ℓ) where

import Algebra.Solver.CommutativeMonoid.Normal as Normal
import Algebra.Solver.Monoid.Solver as Solver

open CommutativeMonoid M using (monoid)

private
  module N = Normal M


------------------------------------------------------------------------
-- Normal forms

open N public
  renaming (correct to normalise-correct)

------------------------------------------------------------------------
-- Proof procedures

open Solver monoid (record { N }) public


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.2

{-# WARNING_ON_USAGE normalise-correct
"Warning: normalise-correct was deprecated in v2.2.
Please use Algebra.Solver.CommutativeMonoid.Normal.correct instead."
#-}
