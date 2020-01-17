------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated monoid solver
{-# OPTIONS --warn=noUserWarning #-}

module Data.List.Solver where

{-# WARNING_ON_IMPORT
"Data.List.Solver was deprecated in v1.3.
Use the new reflective Tactic.MonoidSolver instead."
#-}

import Algebra.Solver.Monoid as Solver
open import Data.List.Properties using (++-monoid)

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _++_

module ++-Solver {a} {A : Set a} =
  Solver (++-monoid A) renaming (id to nil)
