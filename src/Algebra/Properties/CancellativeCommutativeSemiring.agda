------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of operations in CancellativeCommutativeSemiring.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra using (CancellativeCommutativeSemiring)

module Algebra.Properties.CancellativeCommutativeSemiring
  {a ℓ} (R : CancellativeCommutativeSemiring a ℓ)
  where

open import Algebra.Definitions using (AlmostRightCancellative)
open import Data.Sum.Base using (_⊎_; [_,_]′; map₂)
open import Relation.Binary.Definitions using (Decidable)

open CancellativeCommutativeSemiring R
open import Algebra.Consequences.Setoid setoid
open import Relation.Binary.Reasoning.Setoid setoid

*-almostCancelʳ : AlmostRightCancellative _≈_ 0# _*_
*-almostCancelʳ = comm∧almostCancelˡ⇒almostCancelʳ *-comm *-cancelˡ-nonZero

xy≈0⇒x≈0∨y≈0 : Decidable _≈_ → ∀ {x y} → x * y ≈ 0# → x ≈ 0# ⊎ y ≈ 0#
xy≈0⇒x≈0∨y≈0 _≟_ {x} {y} xy≈0 =
  map₂ (λ cancel → cancel y 0# (trans xy≈0 (sym (zeroʳ x)))) (*-cancelˡ-nonZero x)

x≉0∧y≉0⇒xy≉0 : Decidable _≈_ → ∀ {x y} → x ≉ 0# → y ≉ 0# → x * y ≉ 0#
x≉0∧y≉0⇒xy≉0 _≟_ x≉0 y≉0 xy≈0 = [ x≉0 , y≉0 ]′ (xy≈0⇒x≈0∨y≈0 _≟_ xy≈0)

