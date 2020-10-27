------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for commutative semigroup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeSemigroup)
open import Data.Product using (_×_; _,_; map)

module Algebra.Properties.CommutativeSemigroup.Divisibility
  {a ℓ} (CS : CommutativeSemigroup a ℓ)
  where

open CommutativeSemigroup CS

open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------------
-- Re-export the contents of semigroup

open import Algebra.Properties.Semigroup.Divisibility semigroup public

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
