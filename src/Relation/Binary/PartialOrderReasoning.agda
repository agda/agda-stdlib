------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use the
-- Relation.Binary.Reasoning.PartialOrder module directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.PartialOrderReasoning
         {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open import Relation.Binary.Reasoning.PartialOrder P public
