------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a strict partial
-- order.
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
