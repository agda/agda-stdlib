------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures defined over some other
-- structure, like modules and vector spaces
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Properties where

open import Algebra
open import Algebra.Module
open import Level

private
  variable
    c ℓ : Level

self-leftSemimodule : (R : Semiring c ℓ) → LeftSemimodule R c ℓ
self-leftSemimodule semiring = record
  { Carrierᴹ = Carrier
  ; _≈ᴹ_ = _≈_
  ; _+ᴹ_ = _+_
  ; _*ₗ_ = _*_
  ; 0ᴹ = 0#
  ; isLeftSemimodule = record
    { +ᴹ-isCommutativeMonoid = +-isCommutativeMonoid
    ; *ₗ-cong = *-cong
    ; *ₗ-zeroˡ = zeroˡ
    ; *ₗ-distribʳ = distribʳ
    ; *ₗ-identityˡ = *-identityˡ
    ; *ₗ-assoc = *-assoc
    ; *ₗ-zeroʳ = zeroʳ
    ; *ₗ-distribˡ = distribˡ
    }
  } where open Semiring semiring

self-rightSemimodule : (R : Semiring c ℓ) → RightSemimodule R c ℓ
self-rightSemimodule semiring = record
  { Carrierᴹ = Carrier
  ; _≈ᴹ_ = _≈_
  ; _+ᴹ_ = _+_
  ; _*ᵣ_ = _*_
  ; 0ᴹ = 0#
  ; isRightSemimodule = record
    { +ᴹ-isCommutativeMonoid = +-isCommutativeMonoid
    ; *ᵣ-cong = *-cong
    ; *ᵣ-zeroʳ = zeroʳ
    ; *ᵣ-distribˡ = distribˡ
    ; *ᵣ-identityʳ = *-identityʳ
    ; *ᵣ-assoc = *-assoc
    ; *ᵣ-zeroˡ = zeroˡ
    ; *ᵣ-distribʳ = distribʳ
    }
  } where open Semiring semiring

self-semimodule : (R : CommutativeSemiring c ℓ) → Semimodule R c ℓ
self-semimodule commutativeSemiring = record
  { isSemimodule = record
    { isLeftSemimodule =
      let open LeftSemimodule (self-leftSemimodule semiring) in
      isLeftSemimodule
    }
  } where open CommutativeSemiring commutativeSemiring

self-leftModule : (R : Ring c ℓ) → LeftModule R c ℓ
self-leftModule ring = record
  { -ᴹ_ = -_
  ; isLeftModule = record
    { isLeftSemimodule =
      let open LeftSemimodule (self-leftSemimodule semiring) in
      isLeftSemimodule
    ; -ᴹ‿cong = -‿cong
    ; -ᴹ‿inverse = -‿inverse
    }
  } where open Ring ring

self-rightModule : (R : Ring c ℓ) → RightModule R c ℓ
self-rightModule ring = record
  { -ᴹ_ = -_
  ; isRightModule = record
    { isRightSemimodule =
      let open RightSemimodule (self-rightSemimodule semiring) in
      isRightSemimodule
    ; -ᴹ‿cong = -‿cong
    ; -ᴹ‿inverse = -‿inverse
    }
  } where open Ring ring

self-module : (R : CommutativeRing c ℓ) → Module R c ℓ
self-module commutativeRing = record
  { isModule = record
    { isLeftModule =
      let open LeftModule (self-leftModule ring) in isLeftModule
    }
  } where open CommutativeRing commutativeRing
