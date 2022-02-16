{-# OPTIONS --without-K --safe #-}

open import Algebra.Apartness.Bundles using (HeytingCommutativeRing)

module Algebra.Apartness.Properties.HeytingCommutativeRing
  {c ℓ₁ ℓ₂} (HRC : HeytingCommutativeRing c ℓ₁ ℓ₂) where

open import Data.Product using (_,_; proj₂)
open import Algebra.Bundles using (CommutativeRing)

open HeytingCommutativeRing HRC
open CommutativeRing cring using (ring)

open import Algebra.Properties.Ring ring using (-0#≈0#)


1#0 : 1# # 0#
1#0 = proj₂ #⇔invertible ( 1# ,  ( 1*[x-0]≈x , [x-0]*1≈x ) )
  where
    x-0≈x : ∀ {x} → x - 0# ≈ x
    x-0≈x {x} = trans (+-cong refl -0#≈0#) (+-identityʳ x)

    1*[x-0]≈x : ∀ {x} → 1# * (x - 0#) ≈ x
    1*[x-0]≈x {x} = trans (*-identityˡ (x - 0#)) x-0≈x

    [x-0]*1≈x : ∀ {x} → (x - 0#) * 1# ≈ x
    [x-0]*1≈x {x} = trans (*-comm (x - 0#) 1#) 1*[x-0]≈x