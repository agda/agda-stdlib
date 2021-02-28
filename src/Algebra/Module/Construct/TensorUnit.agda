------------------------------------------------------------------------
-- The Agda standard library
--
-- This module constructs the unit of the monoidal structure on
-- R-modules, and similar for weaker module-like structures.
-- The intended universal property is that the maps out of the tensor
-- unit into M are isomorphic to the elements of M.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Construct.TensorUnit where

open import Algebra.Bundles
open import Algebra.Module.Bundles
open import Level

private
  variable
    c ℓ : Level

leftSemimodule : {R : Semiring c ℓ} → LeftSemimodule R c ℓ
leftSemimodule {R = semiring} = record
  { Carrierᴹ = Carrier
  ; _≈ᴹ_ = _≈_
  ; _+ᴹ_ = _+_
  ; _*ₗ_ = _*_
  ; 0ᴹ = 0#
  ; isLeftSemimodule = record
    { +ᴹ-isCommutativeMonoid = +-isCommutativeMonoid
    ; isPreleftSemimodule = record
      { *ₗ-cong = *-cong
      ; *ₗ-zeroˡ = zeroˡ
      ; *ₗ-distribʳ = distribʳ
      ; *ₗ-identityˡ = *-identityˡ
      ; *ₗ-assoc = *-assoc
      ; *ₗ-zeroʳ = zeroʳ
      ; *ₗ-distribˡ = distribˡ
      }
    }
  } where open Semiring semiring

rightSemimodule : {R : Semiring c ℓ} → RightSemimodule R c ℓ
rightSemimodule {R = semiring} = record
  { Carrierᴹ = Carrier
  ; _≈ᴹ_ = _≈_
  ; _+ᴹ_ = _+_
  ; _*ᵣ_ = _*_
  ; 0ᴹ = 0#
  ; isRightSemimodule = record
    { +ᴹ-isCommutativeMonoid = +-isCommutativeMonoid
    ; isPrerightSemimodule = record
      { *ᵣ-cong = *-cong
      ; *ᵣ-zeroʳ = zeroʳ
      ; *ᵣ-distribˡ = distribˡ
      ; *ᵣ-identityʳ = *-identityʳ
      ; *ᵣ-assoc = *-assoc
      ; *ᵣ-zeroˡ = zeroˡ
      ; *ᵣ-distribʳ = distribʳ
      }
    }
  } where open Semiring semiring

bisemimodule : {R : Semiring c ℓ} → Bisemimodule R R c ℓ
bisemimodule {R = semiring} = record
  { isBisemimodule = record
    { +ᴹ-isCommutativeMonoid = +-isCommutativeMonoid
    ; isPreleftSemimodule =
      LeftSemimodule.isPreleftSemimodule leftSemimodule
    ; isPrerightSemimodule =
      RightSemimodule.isPrerightSemimodule rightSemimodule
    ; *ₗ-*ᵣ-assoc = *-assoc
    }
  } where open Semiring semiring

semimodule : {R : CommutativeSemiring c ℓ} → Semimodule R c ℓ
semimodule {R = commutativeSemiring} = record
  { isSemimodule = record
    { isBisemimodule = Bisemimodule.isBisemimodule bisemimodule
    }
  } where open CommutativeSemiring commutativeSemiring

leftModule : {R : Ring c ℓ} → LeftModule R c ℓ
leftModule {R = ring} = record
  { -ᴹ_ = -_
  ; isLeftModule = record
    { isLeftSemimodule = LeftSemimodule.isLeftSemimodule leftSemimodule
    ; -ᴹ‿cong = -‿cong
    ; -ᴹ‿inverse = -‿inverse
    }
  } where open Ring ring

rightModule : {R : Ring c ℓ} → RightModule R c ℓ
rightModule {R = ring} = record
  { -ᴹ_ = -_
  ; isRightModule = record
    { isRightSemimodule = RightSemimodule.isRightSemimodule rightSemimodule
    ; -ᴹ‿cong = -‿cong
    ; -ᴹ‿inverse = -‿inverse
    }
  } where open Ring ring

bimodule : {R : Ring c ℓ} → Bimodule R R c ℓ
bimodule {R = ring} = record
  { isBimodule = record
    { isBisemimodule = Bisemimodule.isBisemimodule bisemimodule
    ; -ᴹ‿cong = -‿cong
    ; -ᴹ‿inverse = -‿inverse
    }
  } where open Ring ring

⟨module⟩ : {R : CommutativeRing c ℓ} → Module R c ℓ
⟨module⟩ {R = commutativeRing} = record
  { isModule = record
    { isBimodule = Bimodule.isBimodule bimodule
    }
  } where open CommutativeRing commutativeRing
