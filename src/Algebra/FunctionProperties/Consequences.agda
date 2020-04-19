------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; Substitutive; Symmetric; Total)

module Algebra.FunctionProperties.Consequences
  {a ℓ} (S : Setoid a ℓ) where

{-# WARNING_ON_IMPORT
"Algebra.FunctionProperties.Consequences was deprecated in v1.3.
Use Algebra.Consequences.Setoid instead."
#-}

open import Algebra.Consequences.Setoid S public
