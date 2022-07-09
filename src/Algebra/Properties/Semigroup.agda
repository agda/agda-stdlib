------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semigroup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semigroup)

module Algebra.Properties.Semigroup {a ℓ} (S : Semigroup a ℓ) where

open Semigroup S

x∙yz≈xy∙z : ∀ x y z → x ∙ (y ∙ z) ≈ (x ∙ y) ∙ z
x∙yz≈xy∙z x y z = sym (assoc x y z)

-- semigroup is LeftAlternative
xx∙y≈x∙xy : ∀ x y → (x ∙ x) ∙ y ≈ x ∙ (x ∙ y)
xx∙y≈x∙xy x y = assoc x x y

-- semigroup is RightAlternative
x∙yy≈xy∙y : ∀ x y → x ∙ (y ∙ y) ≈ (x ∙ y) ∙ y
x∙yy≈xy∙y x y = sym (assoc x y y)

-- semigroup is Flexible
xy∙x≈x∙yx : ∀ x y → (x ∙ y) ∙ x ≈ x ∙ (y ∙ x)
xy∙x≈x∙yx x y = assoc x y x
