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
import Algebra.Solver.Monoid.Tactic as Tactic

open CommutativeMonoid M using (monoid)

------------------------------------------------------------------------
-- Normal forms

open module N = Normal M public

------------------------------------------------------------------------
-- Tactic

open Tactic monoid (record { N }) public
