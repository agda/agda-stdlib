------------------------------------------------------------------------
-- The Agda standard library
--
-- A module used for creating function pipelines, see
-- README.Function.Reasoning for examples
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Function.Reasoning where

open import Function using (_∋_)

-- Need to give _∋_ a new name as syntax cannot contain underscores
infixl 0 ∋-syntax
∋-syntax = _∋_

-- Create ∶ syntax
syntax ∋-syntax A a = a ∶ A

-- Export pipeline functions
open import Function public using (_|>_; _|>′_)
