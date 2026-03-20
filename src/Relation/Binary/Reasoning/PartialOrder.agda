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
--      z  ≡⟨ d≡z ⟨
--      d  ≈⟨ e≈d ⟨
--      e  ∎
--
--    u≈w : u ≈ w
--    u≈w = begin-equality
--      u  ≈⟨ u≈v ⟩
--      v  ≡⟨ v≡w ⟩
--      w  ∎

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (Poset)

module Relation.Binary.Reasoning.PartialOrder
  {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open Poset P
open import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_
  as Strict
  using (_<_)

------------------------------------------------------------------------
-- Re-export contents of base module

open import Relation.Binary.Reasoning.Base.Triple
  isPreorder
  (Strict.<-asym antisym)
  (Strict.<-trans isPartialOrder)
  (Strict.<-resp-≈ isEquivalence ≤-resp-≈)
  Strict.<⇒≤
  (Strict.<-≤-trans Eq.sym trans antisym ≤-respʳ-≈)
  (Strict.≤-<-trans trans antisym ≤-respˡ-≈)
  public
