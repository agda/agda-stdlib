------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions
  using (Substitutive; Symmetric; Total)

module Algebra.FunctionProperties.Consequences
  {a ℓ} (S : Setoid a ℓ) where

{-# WARNING_ON_IMPORT
"Algebra.FunctionProperties.Consequences was deprecated in v1.3.
Use Algebra.Consequences.Setoid instead."
#-}

open import Algebra.Consequences.Setoid S public
