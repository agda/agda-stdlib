------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over unnormalised rationals
------------------------------------------------------------------------

-- See README.Tactic.RingSolver for examples of how to use this solver

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Unnormalised.Tactic.RingSolver where

open import Agda.Builtin.Reflection using (Term; TC)
open import Data.Rational.Unnormalised.Properties using (+-*-commutativeRing; 0≃?-weak)
open import Level using (0ℓ)
open import Data.Unit.Base using (⊤)

import Tactic.RingSolver as Solver using (solve-∀-macro; solve-macro)
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _+_ and _*_

ring : ACR.AlmostCommutativeRing 0ℓ 0ℓ
ring = ACR.fromCommutativeRing
  +-*-commutativeRing
  0≃?-weak

macro
  solve-∀ : Term → TC ⊤
  solve-∀ = Solver.solve-∀-macro (quote ring)

macro
  solve : Term → Term → TC ⊤
  solve n = Solver.solve-macro n (quote ring)
