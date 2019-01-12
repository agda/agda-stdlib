------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a partial order
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.PartialOrder
  {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open Poset P
import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_ as Strict

------------------------------------------------------------------------
-- Re-export contents of base module

open import Relation.Binary.Reasoning.Base.Triple
  isEquivalence
  trans ≤-resp-≈ reflexive
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

-- Version 0.18

infixr 2 _≈⟨⟩_

_≈⟨⟩_ = _≡⟨⟩_
{-# WARNING_ON_USAGE _≈⟨⟩_
"Warning: _≈⟨⟩_ was deprecated in v0.18.
Please use _≡⟨⟩_ instead."
#-}
