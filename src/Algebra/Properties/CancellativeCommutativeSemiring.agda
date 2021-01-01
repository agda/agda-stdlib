------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of operations in CancellativeCommutativeSemiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (CancellativeCommutativeSemiring)
open import Algebra.Definitions using (AlmostRightCancellative)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function using (_$_)
open import Relation.Binary using (Decidable)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

module Algebra.Properties.CancellativeCommutativeSemiring
  {a ℓ} (R : CancellativeCommutativeSemiring a ℓ)
  (open CancellativeCommutativeSemiring R) (_≟_ : Decidable _≈_) where

open EqReasoning setoid

*-cancelʳ-nonZero : AlmostRightCancellative _≈_ 0# _*_
                   -- ∀ {x} y z → ¬ x ≈ e → (y • x) ≈ (z • x) → y ≈ z
                   -- as * is commutative, left and right cancellation
                   -- are equivalent
*-cancelʳ-nonZero {x} y z x≉0 yx≈zx = *-cancelˡ-nonZero y z x≉0 $ begin
  x * y   ≈⟨ *-comm x y ⟩
  y * x   ≈⟨ yx≈zx ⟩
  z * x   ≈⟨ *-comm z x ⟩
  x * z   ∎

x*y≈0⇒x≈0⊎y≈0 : ∀ {x y} → x * y ≈ 0# → x ≈ 0# ⊎ y ≈ 0#
x*y≈0⇒x≈0⊎y≈0 {x} {y} xy≈0 with x ≟ 0# | y ≟ 0#
... | yes x≈0 | _       = inj₁ x≈0
... | no _    | yes y≈0 = inj₂ y≈0
... | no x≉0  | no y≉0  = contradiction y≈0 y≉0
  where
  xy≈x*0 = trans xy≈0 (sym (zeroʳ x));   y≈0 = *-cancelˡ-nonZero y 0# x≉0 xy≈x*0

x≉0∧y≉0⇒xy≉0 : ∀ {x y} → x ≉ 0# → y ≉ 0# → x * y ≉ 0#
x≉0∧y≉0⇒xy≉0 x≉0 y≉0 xy≈0 with x*y≈0⇒x≈0⊎y≈0 xy≈0
... | inj₁ x≈0 = x≉0 x≈0
... | inj₂ y≈0 = y≉0 y≈0
