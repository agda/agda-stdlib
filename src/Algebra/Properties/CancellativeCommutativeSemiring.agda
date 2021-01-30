------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of operations in CancellativeCommutativeSemiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (CancellativeCommutativeSemiring)
open import Algebra.Definitions using (AlmostRightCancellative)
open import Data.Product using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function using (_$_)
open import Relation.Binary using (Decidable)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

module Algebra.Properties.CancellativeCommutativeSemiring
  {a ℓ} (R : CancellativeCommutativeSemiring a ℓ)
  (open CancellativeCommutativeSemiring R) where

open EqReasoning setoid
open import Algebra.Consequences.Setoid setoid
  using (comm+cancelˡ-nonZero⇒cancelʳ-nonZero)
open import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup
  using (x∙yz≈y∙xz)
open import Algebra.Properties.Semiring.Divisibility semiring

*-cancelʳ-nonZero : AlmostRightCancellative _≈_ 0# _*_
*-cancelʳ-nonZero = comm+cancelˡ-nonZero⇒cancelʳ-nonZero *-comm 0# *-cancelˡ-nonZero

x*y≈0⇒x≈0⊎y≈0 : Decidable _≈_ → ∀ {x y} → x * y ≈ 0# → x ≈ 0# ⊎ y ≈ 0#
x*y≈0⇒x≈0⊎y≈0 _≟_ {x} {y} xy≈0 with x ≟ 0# | y ≟ 0#
... | yes x≈0 | _       = inj₁ x≈0
... | no _    | yes y≈0 = inj₂ y≈0
... | no x≉0  | no y≉0  = contradiction y≈0 y≉0
  where
  xy≈x*0 = trans xy≈0 (sym (zeroʳ x));   y≈0 = *-cancelˡ-nonZero y 0# x≉0 xy≈x*0

x≉0∧y≉0⇒xy≉0 : Decidable _≈_ → ∀ {x y} → x ≉ 0# → y ≉ 0# → x * y ≉ 0#
x≉0∧y≉0⇒xy≉0 _≟_ x≉0 y≉0 xy≈0 with x*y≈0⇒x≈0⊎y≈0 _≟_ xy≈0
... | inj₁ x≈0 = x≉0 x≈0
... | inj₂ y≈0 = y≉0 y≈0

xy∣x⇒y∣1 : ∀ {x y} → x ≉ 0# → x * y ∣ x → y ∣ 1#
xy∣x⇒y∣1 {x} {y} x≉0 (q , q*xy≈x) = q , *-cancelˡ-nonZero (q * y) 1# x≉0 (begin
  x * (q * y)  ≈⟨ x∙yz≈y∙xz x q y ⟩
  q * (x * y)  ≈⟨ q*xy≈x ⟩
  x            ≈˘⟨ *-identityʳ x ⟩
  x * 1#       ∎)
