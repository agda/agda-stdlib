------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Heyting Commutative Rings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Apartness.Bundles using (HeytingCommutativeRing)

module Algebra.Apartness.Properties.HeytingCommutativeRing
  {c ℓ₁ ℓ₂} (HCR : HeytingCommutativeRing c ℓ₁ ℓ₂) where

open import Data.Product.Base using (_,_; proj₂)
open import Algebra using (CommutativeRing; RightIdentity)

open HeytingCommutativeRing HCR
open CommutativeRing commutativeRing using (ring)

open import Algebra.Properties.Ring ring using (-0#≈0#)


x-0≈x : RightIdentity _≈_ 0# _-_
x-0≈x x = trans (+-congˡ -0#≈0#) (+-identityʳ x)

1#0 : 1# # 0#
1#0 = invertible⇒# (1# , 1*[x-0]≈x , [x-0]*1≈x)
  where
  1*[x-0]≈x : ∀ {x} → 1# * (x - 0#) ≈ x
  1*[x-0]≈x {x} = trans (*-identityˡ (x - 0#)) (x-0≈x x)

  [x-0]*1≈x : ∀ {x} → (x - 0#) * 1# ≈ x
  [x-0]*1≈x {x} = trans (*-comm (x - 0#) 1#) 1*[x-0]≈x
