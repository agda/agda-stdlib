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

{-# WARNING_ON_IMPORT
"Relation.Binary.PartialOrderReasoning was deprecated in v1.0.
Use Relation.Binary.Reasoning.PartialOrder instead."
#-}
