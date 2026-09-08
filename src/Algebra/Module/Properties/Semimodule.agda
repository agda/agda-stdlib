------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of semimodules.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles        using (CommutativeSemiring)
open import Algebra.Module.Bundles using (Semimodule)
open import Level                  using (Level)

module Algebra.Module.Properties.Semimodule
  {r ℓr m ℓm : Level}
  {semiring  : CommutativeSemiring r ℓr}
  (semimod   : Semimodule semiring m ℓm)
  where

open CommutativeSemiring semiring
open Semimodule          semimod
open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid
open import Relation.Nullary.Negation using (contraposition)

x≈0⇒x*y≈0 : ∀ {x y} → x ≈ 0# → x *ₗ y ≈ᴹ 0ᴹ
x≈0⇒x*y≈0 {x} {y} x≈0 = begin
  x  *ₗ y ≈⟨ *ₗ-congʳ x≈0 ⟩
  0# *ₗ y ≈⟨ *ₗ-zeroˡ y ⟩
  0ᴹ      ∎

y≈0⇒x*y≈0 : ∀ {x y} → y ≈ᴹ 0ᴹ → x *ₗ y ≈ᴹ 0ᴹ
y≈0⇒x*y≈0 {x} {y} y≈0 = begin
  x *ₗ y  ≈⟨ *ₗ-congˡ y≈0 ⟩
  x *ₗ 0ᴹ ≈⟨ *ₗ-zeroʳ x ⟩
  0ᴹ      ∎

x*y≉0⇒x≉0 : ∀ {x y} → x *ₗ y ≉ᴹ 0ᴹ → x ≉ 0#
x*y≉0⇒x≉0 = contraposition x≈0⇒x*y≈0

x*y≉0⇒y≉0 : ∀ {x y} → x *ₗ y ≉ᴹ 0ᴹ → y ≉ᴹ 0ᴹ
x*y≉0⇒y≉0 = contraposition y≈0⇒x*y≈0
