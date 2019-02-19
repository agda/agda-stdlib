------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use the
-- Relation.Binary.Reasoning.StrictPartialOrder module directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.StrictPartialOrderReasoning
         {p₁ p₂ p₃} (S : StrictPartialOrder p₁ p₂ p₃) where

open import Relation.Binary.Reasoning.StrictPartialOrder S public
