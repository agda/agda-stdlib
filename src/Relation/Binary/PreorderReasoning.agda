------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use the
-- Relation.Binary.Reasoning.Preorder module directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.PreorderReasoning
         {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where

open import Relation.Binary.Reasoning.Preorder P public
