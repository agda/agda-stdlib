------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over booleans
------------------------------------------------------------------------

-- See README.Nat for examples of how to use similar solvers

module Data.Bool.Solver where

import Algebra.Solver.Ring.Simple as Solver
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
open import Data.Bool using (_≟_)
open import Data.Bool.Properties

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _∨_ and _∧_

module RingSolver =
  Solver (ACR.fromCommutativeSemiring ∨-∧-commutativeSemiring) _≟_

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _xor_ and _∧_

module XorRingSolver =
  Solver (ACR.fromCommutativeRing xor-∧-commutativeRing) _≟_
