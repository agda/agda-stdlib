------------------------------------------------------------------------
-- The Agda standard library
--
-- Some simple use cases of the ring solver
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.RingSolver.Examples where

open import Algebra

open import Data.Integer.Base using (ℤ)
open import Data.Integer.Properties
open import Data.Maybe

open import Agda.Builtin.Equality using (_≡_ ; refl)

open import Tactic.RingSolver
open import Tactic.RingSolver.Core.AlmostCommutativeRing


module IntegerExamples where
  ℤAsCRing : CommutativeRing _ _
  ℤAsCRing = record
               { Carrier = ℤ
               ; _≈_ = _
               ; _+_ = _
               ; _*_ = _
               ; -_ = _
               ; 0# = _
               ; 1# = _
               ; isCommutativeRing = +-*-isCommutativeRing
               }

  ℤAsAlmostCRing : _
  ℤAsAlmostCRing = fromCommutativeRing ℤAsCRing (λ _ → nothing)
  open AlmostCommutativeRing ℤAsAlmostCRing

  works : ∀ x y → x + y ≡ y + x
  works = solve-∀ ℤAsAlmostCRing

  {-
  nope : ∀ x y → (x + y) * (x - y) ≡ (x * x) - (y * y)
  nope = solve-∀ ℤAsAlmostCRing
  -}

module GenericExamples {r s} (R : CommutativeRing r s) where
  RAsAlmostCRing = fromCommutativeRing R (λ _ → nothing)
  open AlmostCommutativeRing RAsAlmostCRing

  works : ∀ x y → x + y ≈ y + x
  works = solve-∀ RAsAlmostCRing

  {-
  nope : ∀ x y → (x + y) * (x - y) ≡ (x * x) - (y * y)
  nope = solve-∀ RAsAlmostCRing
  -}

module SolverCanOnlyUseNames {r s} (R : CommutativeRing r s) where
  RAsAlmostCRing = fromCommutativeRing R (λ _ → nothing)
  open AlmostCommutativeRing RAsAlmostCRing

  {-
  nope : ∀ x y → x + y ≈ y + x
  nope = solve-∀ (fromCommutativeRing R (λ _ → nothing))
  -}

  {-
    to make this work, one has to lift deBruijn indices in the expression defining the ring
  -}
