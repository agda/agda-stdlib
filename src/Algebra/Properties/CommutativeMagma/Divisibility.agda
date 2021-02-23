------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over commutative magmas
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeMagma)
open import Data.Product using (_×_; _,_; map)

module Algebra.Properties.CommutativeMagma.Divisibility
  {a ℓ} (CM : CommutativeMagma a ℓ)
  where

open CommutativeMagma CM

open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------------
-- Re-export the contents of magmas

open import Algebra.Properties.Magma.Divisibility magma public

------------------------------------------------------------------------------
-- Further properties

x∣xy : ∀ x y → x ∣ x ∙ y
x∣xy x y = y , comm y x

xy≈z⇒x∣z : ∀ x y {z} → x ∙ y ≈ z → x ∣ z
xy≈z⇒x∣z x y xy≈z = ∣-respʳ xy≈z (x∣xy x y)

∣-factors : ∀ x y → (x ∣ x ∙ y) × (y ∣ x ∙ y)
∣-factors x y = x∣xy x y , x∣yx y x

∣-factors-≈ : ∀ x y {z} → x ∙ y ≈ z → x ∣ z × y ∣ z
∣-factors-≈ x y xy≈z = xy≈z⇒x∣z x y xy≈z , xy≈z⇒y∣z x y xy≈z
