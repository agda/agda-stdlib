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
