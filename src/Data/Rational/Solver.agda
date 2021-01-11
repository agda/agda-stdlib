------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over rationals
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Solver where

import Algebra.Solver.Ring.Simple as Solver
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
open import Data.Rational.Properties using (_≟_; +-*-commutativeRing)

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _+_ and _*_

module +-*-Solver =
  Solver (ACR.fromCommutativeRing +-*-commutativeRing) _≟_
