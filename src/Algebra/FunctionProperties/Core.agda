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
