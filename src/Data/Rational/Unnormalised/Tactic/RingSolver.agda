------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solvers for equations over unnormalised rationals
------------------------------------------------------------------------

-- See README.Integer for examples of how to use this solver

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Unnormalised.Tactic.RingSolver where

open import Agda.Builtin.Reflection

open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Data.Nat.Base using (zero; suc)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Rational.Unnormalised.Base using (ℚᵘ; 0ℚᵘ; _≃_; mkℚᵘ; *≡*)
open import Data.Rational.Unnormalised.Properties using (+-*-commutativeRing)
open import Level using (0ℓ)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (refl)

import Tactic.RingSolver as Solver
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _+_ and _*_

ring : ACR.AlmostCommutativeRing 0ℓ 0ℓ
ring = ACR.fromCommutativeRing +-*-commutativeRing f
  where
   f : (x : ℚᵘ) → Maybe (0ℚᵘ ≃ x)
   f (mkℚᵘ (pos zero)    _) = just (*≡* refl)
   f (mkℚᵘ (pos (suc _)) _) = nothing
   f (mkℚᵘ (negsuc _)    _) = nothing

macro
  solve-∀ : Term → TC ⊤
  solve-∀ = Solver.solve-∀-macro (quote ring)

macro
  solve : Term → Term → TC ⊤
  solve n = Solver.solve-macro n (quote ring)
