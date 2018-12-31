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
  trans ≤-resp-≈ refl
  (Strict.trans isPartialOrder)
  (Strict.<-resp-≈ isEquivalence ≤-resp-≈)
  Strict.<⇒≤
  (Strict.<-≤-trans Eq.sym trans antisym ≤-respʳ-≈)
  (Strict.≤-<-trans trans antisym ≤-respˡ-≈)
  public
