------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over integers
------------------------------------------------------------------------

-- See README.Nat for examples of how to use similar solvers

module Data.Integer.Solver where

import Algebra.Solver.Ring.Simple as Solver
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
open import Data.Integer using (_≟_)
open import Data.Integer.Properties using (+-*-commutativeRing)

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _+_ and _*_

-- A module for automatically solving propositional equivalences
module RingSolver =
  Solver (ACR.fromCommutativeRing +-*-commutativeRing) _≟_
