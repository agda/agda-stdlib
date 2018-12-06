------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over lists
------------------------------------------------------------------------

-- See README.Nat for examples of how to use similar solvers

{-# OPTIONS --without-K #-}

module Data.List.Solver where

import Algebra.Solver.Monoid as Solver
open import Data.List.Properties using (++-monoid)

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _++_

module ++-Solver {a} {A : Set a} =
  Solver (++-monoid A) renaming (id to nil)
