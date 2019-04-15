------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Algebra.FunctionProperties. They are placed here because
-- Algebra.FunctionProperties is a parameterised module, and some of
-- the parameters are irrelevant for these definitions.

{-# OPTIONS --without-K --safe #-}

module Algebra.FunctionProperties.Core where

open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Level
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Unary and binary operations

Op₁ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₁ A = A → A

Op₂ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₂ A = A → A → A

------------------------------------------------------------------------
-- Interactions of binary operations and predicates

module _ {a p} {A : Set a} (_∙_ : Op₂ A) (P : Pred A p) where

  -- The operation preserves the predicate holding on the result

  PreservesLeft : Set _
  PreservesLeft = ∀ {a} b → P a → P (a ∙ b)

  PreservesRight : Set _
  PreservesRight = ∀ a {b} → P b → P (a ∙ b)

  PreservesOne : Set _
  PreservesOne  = ∀ a b → P a ⊎ P b → P (a ∙ b)

  PreservesBoth : Set _
  PreservesBoth = ∀ {a b} → P a → P b → P (a ∙ b)

  -- The operation forces the predicate to hold on the arguments

  ForcesLeft : Set _
  ForcesLeft = ∀ a b → P (a ∙ b) → P a

  ForcesRight : Set _
  ForcesRight = ∀ a b → P (a ∙ b) → P b

  ForcesOne : Set _
  ForcesOne = ∀ a b → P (a ∙ b) → P a ⊎ P b

  ForcesBoth : Set _
  ForcesBoth = ∀ a b → P (a ∙ b) → P a × P b
