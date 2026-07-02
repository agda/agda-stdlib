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

open import Data.Sum.Base using (_⊎_; [_,_]′; map₂)
open import Relation.Binary.Definitions using (Decidable)

open CancellativeCommutativeSemiring R renaming (Carrier to A)

private
  variable
    x y : A


module _ (_≈?_ : Decidable _≈_) where

  xy≈0⇒x≈0∨y≈0 : x * y ≈ 0# → x ≈ 0# ⊎ y ≈ 0#
  xy≈0⇒x≈0∨y≈0 {x} {y} xy≈0 =
    map₂ (λ cancel → cancel _ _ (trans xy≈0 (sym (zeroʳ x)))) (*-cancelˡ-nonZero x)

  x≉0∧y≉0⇒xy≉0 : x ≉ 0# → y ≉ 0# → x * y ≉ 0#
  x≉0∧y≉0⇒xy≉0 x≉0 y≉0 xy≈0 = [ x≉0 , y≉0 ]′ (xy≈0⇒x≈0∨y≈0 xy≈0)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 3.0

*-almostCancelʳ = *-cancelʳ-nonZero
{-# WARNING_ON_USAGE *-almostCancelʳ
"Warning: *-almostCancelʳ was deprecated in v3.0.
Please use Algebra.Structures.IsCancellativeCommutativeSemiring.*-cancelʳ-nonZero instead."
#-}
