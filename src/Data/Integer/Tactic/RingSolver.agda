------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over integers
------------------------------------------------------------------------

-- See README.Tactic.RingSolver for examples of how to use this solver

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Integer.Tactic.RingSolver where

open import Agda.Builtin.Reflection

open import Data.Maybe.Base using (just; nothing)
open import Data.Integer.Base using (+0)
open import Data.Integer.Properties using (+-*-commutativeRing)
open import Level using (0ℓ)
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality.Core using (refl)
import Tactic.RingSolver as Solver
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _+_ and _*_

ring : ACR.AlmostCommutativeRing 0ℓ 0ℓ
ring = ACR.fromCommutativeRing +-*-commutativeRing
  λ { +0 → just refl; _ → nothing }

macro
  solve-∀ : Term → TC ⊤
  solve-∀ = Solver.solve-∀-macro (quote ring)

macro
  solve : Term → Term → TC ⊤
  solve n = Solver.solve-macro n (quote ring)
