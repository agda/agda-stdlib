------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over naturals
------------------------------------------------------------------------

-- See README.Nat for examples of how to use this solver

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Solver where

import Algebra.Solver.Ring.Simple as Solver
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
open import Data.Nat.Properties

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _+_ and _*_

module +-*-Solver =
  Solver (ACR.fromCommutativeSemiring *-+-commutativeSemiring) _≟_
