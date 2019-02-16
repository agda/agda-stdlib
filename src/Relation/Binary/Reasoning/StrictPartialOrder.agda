------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a strict partial
-- order.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.StrictPartialOrder
  {p₁ p₂ p₃} (S : StrictPartialOrder p₁ p₂ p₃) where

open StrictPartialOrder S
import Relation.Binary.Construct.StrictToNonStrict _≈_ _<_ as NonStrict

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Relation.Binary.Reasoning.Base.Triple
  (NonStrict.isPreorder₂ isStrictPartialOrder)
  trans
  <-resp-≈
  NonStrict.<⇒≤
  (NonStrict.<-≤-trans trans <-respʳ-≈)
  public
