------------------------------------------------------------------------
-- The Agda standard library
--
-- Issue #2875: this is a stub module, retained solely for compatibility
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Morphism.Definitions
  {a} (A : Set a)     -- The domain of the morphism
  {b} (B : Set b)     -- The codomain of the morphism
  where

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.4

open import Function.Core public
  using (Morphism)
{-# WARNING_ON_USAGE Morphism
"Warning: Morphism was deprecated in v2.4.
Please use the standard function notation (e.g. A → B) instead."
#-}

open import Function.Definitions public
  using ()
  renaming (Congruent to Homomorphic₂)
{-# WARNING_ON_USAGE Homomorphic₂
"Warning: Homomorphic₂ was deprecated in v2.4.
Please use Function.Definitions.Congruent instead."
#-}
