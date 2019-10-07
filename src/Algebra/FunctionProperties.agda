------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use `Algebra` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)

module Algebra.FunctionProperties
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Algebra.Core public
open import Algebra.Definitions _≈_ public
