------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semigroup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semigroup)

module Algebra.Properties.Semigroup {a ℓ} (S : Semigroup a ℓ) where

open Semigroup S
open import Algebra.Definitions _≈_

x∙yz≈xy∙z : ∀ x y z → x ∙ (y ∙ z) ≈ (x ∙ y) ∙ z
x∙yz≈xy∙z x y z = sym (assoc x y z)

-- semigroup is LeftAlternative
leftAlternative : LeftAlternative _∙_
leftAlternative x y = assoc x x y

-- semigroup is RightAlternative
rightAlternative : RightAlternative _∙_
rightAlternative x y = sym (assoc x y y)

-- semigroup is Flexible
flexible : Flexible _∙_
flexible x y = assoc x y x
