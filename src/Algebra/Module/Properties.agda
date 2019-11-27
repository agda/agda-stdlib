------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures defined over some other
-- structure, like modules and vector spaces
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Properties where

open import Algebra.Bundles
open import Algebra.Module.Bundles
open import Level

private
  variable
    c ℓ : Level

semiring⇒leftSemimodule : (R : Semiring c ℓ) → LeftSemimodule R c ℓ
semiring⇒leftSemimodule semiring = record
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

semiring⇒rightSemimodule : (R : Semiring c ℓ) → RightSemimodule R c ℓ
semiring⇒rightSemimodule semiring = record
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

commutativeSemiring⇒semimodule :
  (R : CommutativeSemiring c ℓ) → Semimodule R c ℓ
commutativeSemiring⇒semimodule commutativeSemiring = record
  { isSemimodule = record
    { isBisemimodule = record
      { +ᴹ-isCommutativeMonoid = +-isCommutativeMonoid
      ; isPreleftSemimodule =
        LeftSemimodule.isPreleftSemimodule (semiring⇒leftSemimodule semiring)
      ; isPrerightSemimodule =
        RightSemimodule.isPrerightSemimodule (semiring⇒rightSemimodule semiring)
      ; *ₗ-*ᵣ-assoc = *-assoc
      }
    }
  } where open CommutativeSemiring commutativeSemiring

ring⇒leftModule : (R : Ring c ℓ) → LeftModule R c ℓ
ring⇒leftModule ring = record
  { -ᴹ_ = -_
  ; isLeftModule = record
    { isLeftSemimodule =
      LeftSemimodule.isLeftSemimodule (semiring⇒leftSemimodule semiring)
    ; -ᴹ‿cong = -‿cong
    ; -ᴹ‿inverse = -‿inverse
    }
  } where open Ring ring

ring⇒rightModule : (R : Ring c ℓ) → RightModule R c ℓ
ring⇒rightModule ring = record
  { -ᴹ_ = -_
  ; isRightModule = record
    { isRightSemimodule =
      RightSemimodule.isRightSemimodule (semiring⇒rightSemimodule semiring)
    ; -ᴹ‿cong = -‿cong
    ; -ᴹ‿inverse = -‿inverse
    }
  } where open Ring ring

-- TODO: #898 would allow refactoring using
-- Semimodule.isBisemimodule
--  (commutativeSemiring⇒semimodule commutativeSemiring)
commutativeRing⇒module : (R : CommutativeRing c ℓ) → Module R c ℓ
commutativeRing⇒module commutativeRing = record
  { isModule = record
    { isBimodule = record
      { isBisemimodule = record
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
        ; isPrerightSemimodule = record
          { *ᵣ-cong = *-cong
          ; *ᵣ-zeroʳ = zeroʳ
          ; *ᵣ-distribˡ = distribˡ
          ; *ᵣ-identityʳ = *-identityʳ
          ; *ᵣ-assoc = *-assoc
          ; *ᵣ-zeroˡ = zeroˡ
          ; *ᵣ-distribʳ = distribʳ
          }
        ; *ₗ-*ᵣ-assoc = *-assoc
        }
      ; -ᴹ‿cong = -‿cong
      ; -ᴹ‿inverse = -‿inverse
      }
    }
  } where open CommutativeRing commutativeRing
