------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use the
-- Relation.Binary.Reasoning.Setoid module directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.EqReasoning {s₁ s₂} (S : Setoid s₁ s₂) where

open import Relation.Binary.Reasoning.Setoid S public

{-# WARNING_ON_IMPORT
"Relation.Binary.EqReasoning was deprecated in v1.0.
Use Relation.Binary.Reasoning.Setoid instead."
#-}
