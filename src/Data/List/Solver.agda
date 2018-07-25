------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over lists
------------------------------------------------------------------------

-- See README.Nat for examples of how to use similar solvers

module Data.List.Solver where

open import Algebra.Solver.Monoid
open import Data.List.Properties using (++-monoid)

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _++_

module List-solver {a} {A : Set a} =
  Algebra.Solver.Monoid (++-monoid A) renaming (id to nil)
