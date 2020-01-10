------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over integers
------------------------------------------------------------------------

-- See README.Integer for examples of how to use this solver

{-# OPTIONS --without-K --safe #-}

module Data.Integer.Tactic.RingSolver where

open import Agda.Builtin.Reflection

open import Data.Maybe using (just; nothing)
open import Data.Nat.Base using (zero; suc)
open import Data.Nat.Properties
open import Level using (0ℓ)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality
import Tactic.RingSolver as Solver
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _+_ and _*_

ring : ACR.AlmostCommutativeRing 0ℓ 0ℓ
ring = ACR.fromCommutativeSemiring *-+-commutativeSemiring
  λ { zero → just refl; _ → nothing }

macro
  solve : Term → TC ⊤
  solve = Solver.solve-macro (quote ring)

macro
  solveOver : Term → Term → TC ⊤
  solveOver n = Solver.solveOver-macro n (quote ring)
