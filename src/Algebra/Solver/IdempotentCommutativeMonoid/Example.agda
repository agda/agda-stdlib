------------------------------------------------------------------------
-- The Agda standard library
--
-- An example of how Algebra.IdempotentCommutativeMonoidSolver can be
-- used
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Solver.IdempotentCommutativeMonoid.Example where

import Algebra.Solver.IdempotentCommutativeMonoid as ICM-Solver

open import Data.Bool.Base using (_∨_)
open import Data.Bool.Properties using (∨-idempotentCommutativeMonoid)
open import Data.Fin.Base using (zero; suc)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

open ICM-Solver ∨-idempotentCommutativeMonoid

test : ∀ x y z → (x ∨ y) ∨ (x ∨ z) ≡ (z ∨ y) ∨ x
test a b c = let _∨_ = _⊕_ in
  prove 3 ((x ∨ y) ∨ (x ∨ z)) ((z ∨ y) ∨ x) (a ∷ b ∷ c ∷ [])
  where
  x = var zero
  y = var (suc zero)
  z = var (suc (suc zero))
