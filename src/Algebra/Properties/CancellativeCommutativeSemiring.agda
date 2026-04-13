------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of operations in CancellativeCommutativeSemiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CancellativeCommutativeSemiring)

module Algebra.Properties.CancellativeCommutativeSemiring
  {a ℓ} (R : CancellativeCommutativeSemiring a ℓ)
  where

open import Algebra.Definitions using (AlmostRightCancellative)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open CancellativeCommutativeSemiring R
open import Algebra.Consequences.Setoid setoid
open import Relation.Binary.Reasoning.Setoid setoid

*-almostCancelʳ : AlmostRightCancellative _≈_ 0# _*_
*-almostCancelʳ = comm∧almostCancelˡ⇒almostCancelʳ *-comm *-cancelˡ-nonZero

xy≈0⇒x≈0∨y≈0 : Decidable _≈_ → ∀ {x y} → x * y ≈ 0# → x ≈ 0# ⊎ y ≈ 0#
xy≈0⇒x≈0∨y≈0 _≟_ {x} {y} xy≈0 with x ≟ 0# | y ≟ 0#
... | yes x≈0 | _       = inj₁ x≈0
... | no  _   | yes y≈0 = inj₂ y≈0
... | no  x≉0 | no  y≉0 = contradiction y≈0 y≉0
  where
  xy≈x*0 = trans xy≈0 (sym (zeroʳ x))
  y≈0    = *-cancelˡ-nonZero _ y 0# x≉0 xy≈x*0

x≉0∧y≉0⇒xy≉0 : Decidable _≈_ → ∀ {x y} → x ≉ 0# → y ≉ 0# → x * y ≉ 0#
x≉0∧y≉0⇒xy≉0 _≟_ x≉0 y≉0 xy≈0 with xy≈0⇒x≈0∨y≈0 _≟_ xy≈0
... | inj₁ x≈0 = x≉0 x≈0
... | inj₂ y≈0 = y≉0 y≈0
