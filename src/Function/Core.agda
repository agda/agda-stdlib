------------------------------------------------------------------------
-- The Agda standard library
--
-- Core definitions for Functions
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

{-# OPTIONS --without-K --safe #-}

module Function.Core where

------------------------------------------------------------------------
-- Types

Fun₁ : ∀ {a} → Set a → Set a
Fun₁ A = A → A

Fun₂ : ∀ {a} → Set a → Set a
Fun₂ A = A → A → A
