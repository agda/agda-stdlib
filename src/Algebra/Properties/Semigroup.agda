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
leftAlternative : ∀ x y → (x ∙ x) ∙ y ≈ x ∙ (x ∙ y)
leftAlternative x y = assoc x x y

-- semigroup is RightAlternative
rightAlternative : ∀ x y → x ∙ (y ∙ y) ≈ (x ∙ y) ∙ y
rightAlternative x y = sym (assoc x y y)

-- semigroup is Flexible
flexible : ∀ x y → (x ∙ y) ∙ x ≈ x ∙ (y ∙ x)
flexible x y = assoc x y x
