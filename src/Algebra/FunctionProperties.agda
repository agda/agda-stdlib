------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use `Algebra` or
-- `Algebra.Definitions` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)

module Algebra.FunctionProperties {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Algebra.Core public
open import Algebra.Definitions _≈_ public
