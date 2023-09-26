------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semigroup
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra using (Semigroup)

module Algebra.Properties.Semigroup {a ℓ} (S : Semigroup a ℓ) where

open Semigroup S
open import Algebra.Definitions _≈_
open import Data.Product.Base using (_,_)

x∙yz≈xy∙z : ∀ x y z → x ∙ (y ∙ z) ≈ (x ∙ y) ∙ z
x∙yz≈xy∙z x y z = sym (assoc x y z)

alternativeˡ : LeftAlternative _∙_
alternativeˡ x y = assoc x x y

alternativeʳ : RightAlternative _∙_
alternativeʳ x y = sym (assoc x y y)

alternative : Alternative _∙_
alternative = alternativeˡ , alternativeʳ

flexible : Flexible _∙_
flexible x y = assoc x y x
