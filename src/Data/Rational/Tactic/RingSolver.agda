------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over rationals
------------------------------------------------------------------------

-- See README.Integer for examples of how to use this solver

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Tactic.RingSolver where

open import Agda.Builtin.Reflection using (Term; TC)

open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Data.Nat.Base using (zero; suc)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Rational.Base using (ℚ; 0ℚ; mkℚ)
open import Data.Rational.Properties using (+-*-commutativeRing)
open import Level using (0ℓ)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Tactic.RingSolver as Solver using (solve-macro; solve-∀-macro)
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _+_ and _*_

ring : ACR.AlmostCommutativeRing 0ℓ 0ℓ
ring = ACR.fromCommutativeRing +-*-commutativeRing f
  where
   f : (x : ℚ) → Maybe (0ℚ ≡ x)
   f (mkℚ (pos 0)       0       _) = just refl
   f (mkℚ (pos 0)       (suc _) _) = nothing
   f (mkℚ (pos (suc _)) _       _) = nothing
   f (mkℚ (negsuc _)    _       _) = nothing

macro
  solve-∀ : Term → TC ⊤
  solve-∀ = Solver.solve-∀-macro (quote ring)

macro
  solve : Term → Term → TC ⊤
  solve n = Solver.solve-macro n (quote ring)
