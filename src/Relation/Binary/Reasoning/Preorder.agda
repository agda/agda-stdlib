------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a preorder
------------------------------------------------------------------------

-- Example uses:
--
--    u∼y : u ∼ y
--    u∼y = begin
--      u  ≈⟨ u≈v ⟩
--      v  ≡⟨ v≡w ⟩
--      w  ∼⟨ w∼y ⟩
--      y  ≈⟨ z≈y ⟩
--      z  ∎
--
--    u≈w : u ≈ w
--    u≈w = begin-equality
--      u  ≈⟨ u≈v ⟩
--      v  ≡⟨ v≡w ⟩
--      w  ≡˘⟨ x≡w ⟩
--      x  ∎

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.Preorder
  {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where

open Preorder P

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Relation.Binary.Reasoning.Base.Double isPreorder public


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.0

infixr 2 _≈⟨⟩_

_≈⟨⟩_ = _≡⟨⟩_
{-# WARNING_ON_USAGE _≈⟨⟩_
"Warning: _≈⟨⟩_ was deprecated in v1.0.
Please use _≡⟨⟩_ instead."
#-}
