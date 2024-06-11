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

------------------------------------------------------------------------
-- Tactic

open Tactic monoid (record { N }) public
