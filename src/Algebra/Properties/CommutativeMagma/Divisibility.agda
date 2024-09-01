------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over commutative magmas
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra using (CommutativeMagma)

module Algebra.Properties.CommutativeMagma.Divisibility
  {a ℓ} (CM : CommutativeMagma a ℓ)
  where

open import Data.Product.Base using (_×_; _,_)

open CommutativeMagma CM using (magma; _≈_; _∙_; comm)

------------------------------------------------------------------------
-- Re-export the contents of magmas

open import Algebra.Properties.Magma.Divisibility magma public

------------------------------------------------------------------------
-- Further properties

x∣xy : ∀ x y → x ∣ x ∙ y
x∣xy x y = y , comm y x

xy≈z⇒x∣z : ∀ x y {z} → x ∙ y ≈ z → x ∣ z
xy≈z⇒x∣z x y xy≈z = ∣-respʳ xy≈z (x∣xy x y)

x|xy∧y|xy : ∀ x y → (x ∣ x ∙ y) × (y ∣ x ∙ y)
x|xy∧y|xy x y = x∣xy x y , x∣yx y x

xy≈z⇒x|z∧y|z : ∀ x y {z} → x ∙ y ≈ z → x ∣ z × y ∣ z
xy≈z⇒x|z∧y|z x y xy≈z = xy≈z⇒x∣z x y xy≈z , xy≈z⇒y∣z x y xy≈z


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.2

∣-factors = x|xy∧y|xy
{-# WARNING_ON_USAGE ∣-factors
"Warning: ∣-factors was deprecated in v2.2.
Please use x|xy∧y|xy instead. "
#-}
∣-factors-≈ = xy≈z⇒x|z∧y|z
{-# WARNING_ON_USAGE ∣-factors-≈
"Warning: ∣-factors-≈ was deprecated in v2.2.
Please use xy≈z⇒x|z∧y|z instead. "
#-}
