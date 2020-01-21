------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use `Algebra` or
-- `Algebra.Definitions` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)

module Algebra.FunctionProperties {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

{-# WARNING_ON_IMPORT
"Algebra.FunctionProperties was deprecated in v1.2.
Use Algebra.Definitions instead."
#-}

open import Algebra.Core public
open import Algebra.Definitions _≈_ public
