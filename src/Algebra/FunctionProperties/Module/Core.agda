------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions where two carrier sets are involved
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Algebra.FunctionProperties.Module. They are placed here because
-- Algebra.FunctionProperties.Module is a parameterised module, and some of
-- the parameters are irrelevant for these definitions.

{-# OPTIONS --without-K --safe #-}

module Algebra.FunctionProperties.Module.Core where

open import Level

------------------------------------------------------------------------
-- Binary operations

Opₗ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Opₗ A B = A → B → B

Opᵣ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Opᵣ A B = B → A → B
