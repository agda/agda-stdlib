------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a partial order
------------------------------------------------------------------------

-- Example uses:
--
--    u≤x : u ≤ x
--    u≤x = begin
--      u  ≈⟨ u≈v ⟩
--      v  ≡⟨ v≡w ⟩
--      w  <⟨ w≤x ⟩
--      x  ∎
--
--    u<x : u < x
--    u<x = begin-strict
--      u  ≈⟨ u≈v ⟩
--      v  ≡⟨ v≡w ⟩
--      w  <⟨ w≤x ⟩
--      x  ∎
--
--    u<e : u < e
--    u<e = begin-strict
--      u  ≈⟨ u≈v ⟩
--      v  ≡⟨ v≡w ⟩
--      w  <⟨ w<x ⟩
--      x  ≤⟨ x≤y ⟩
--      y  <⟨ y<z ⟩
--      z  ≡˘⟨ d≡z ⟩
--      d  ≈˘⟨ e≈d ⟩
--      e  ∎
--
--    u≈w : u ≈ w
--    u≈w = begin-equality
--      u  ≈⟨ u≈v ⟩
--      v  ≡⟨ v≡w ⟩
--      w  ∎

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.PartialOrder
  {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open Poset P
import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_ as Strict

------------------------------------------------------------------------
-- Re-export contents of base module

open import Relation.Binary.Reasoning.Base.Triple
  isPreorder
  (Strict.trans isPartialOrder)
  (Strict.<-resp-≈ isEquivalence ≤-resp-≈)
  Strict.<⇒≤
  (Strict.<-≤-trans Eq.sym trans antisym ≤-respʳ-≈)
  (Strict.≤-<-trans trans antisym ≤-respˡ-≈)
  public



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
