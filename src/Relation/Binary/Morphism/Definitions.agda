------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for morphisms between algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Morphism.Definitions
  {a} (A : Set a)     -- The domain of the morphism
  {b} (B : Set b)     -- The codomain of the morphism
  where

------------------------------------------------------------------------
-- Morphism definition in Function.Core

open import Function.Core public
  using (Morphism)

------------------------------------------------------------------------
-- Basic definitions

open import Function.Definitions public
  using ()
  renaming (Congruent to Homomorphic₂)
