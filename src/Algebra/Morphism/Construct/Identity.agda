------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity morphism for algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Algebra.Morphism.Construct.Identity where

open import Algebra.Bundles
open import Algebra.Morphism.Structures
  using ( module MagmaMorphisms
        ; module MonoidMorphisms
        ; module GroupMorphisms
        ; module NearSemiringMorphisms
        ; module SemiringMorphisms
        ; module RingMorphisms
        )
open import Data.Product using (_,_)
open import Function.Base using (id)
open import Level using (Level)
open import Relation.Binary.Morphism.Construct.Identity using (isRelHomomorphism)
open import Relation.Binary.Definitions using (Reflexive)

private
  variable
    c ℓ : Level

module _ (M : RawMagma c ℓ) (open RawMagma M) (refl : Reflexive _≈_) where
  open MagmaMorphisms M M

  isMagmaHomomorphism : IsMagmaHomomorphism id
  isMagmaHomomorphism = record
    { isRelHomomorphism = isRelHomomorphism _
    ; homo              = λ _ _ → refl
    }

  isMagmaMonomorphism : IsMagmaMonomorphism id
  isMagmaMonomorphism = record
    { isMagmaHomomorphism = isMagmaHomomorphism
    ; injective = id
    }

  isMagmaIsomorphism : IsMagmaIsomorphism id
  isMagmaIsomorphism = record
    { isMagmaMonomorphism = isMagmaMonomorphism
    ; surjective = _, refl
    }

module _ (M : RawMonoid c ℓ) (open RawMonoid M) (refl : Reflexive _≈_) where
  open MonoidMorphisms M M

  isMonoidHomomorphism : IsMonoidHomomorphism id
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = isMagmaHomomorphism _ refl
    ; ε-homo = refl
    }

  isMonoidMonomorphism : IsMonoidMonomorphism id
  isMonoidMonomorphism = record
    { isMonoidHomomorphism = isMonoidHomomorphism
    ; injective = id
    }

  isMonoidIsomorphism : IsMonoidIsomorphism id
  isMonoidIsomorphism = record
    { isMonoidMonomorphism = isMonoidMonomorphism
    ; surjective = _, refl
    }

module _ (G : RawGroup c ℓ) (open RawGroup G) (refl : Reflexive _≈_) where
  open GroupMorphisms G G

  isGroupHomomorphism : IsGroupHomomorphism id
  isGroupHomomorphism = record
    { isMonoidHomomorphism = isMonoidHomomorphism _ refl
    ; ⁻¹-homo = λ _ → refl
    }

  isGroupMonomorphism : IsGroupMonomorphism id
  isGroupMonomorphism = record
    { isGroupHomomorphism = isGroupHomomorphism
    ; injective = id
    }

  isGroupIsomorphism : IsGroupIsomorphism id
  isGroupIsomorphism = record
    { isGroupMonomorphism = isGroupMonomorphism
    ; surjective = _, refl
    }

module _ (R : RawNearSemiring c ℓ) (open RawNearSemiring R) (refl : Reflexive _≈_) where
  open NearSemiringMorphisms R R

  isNearSemiringHomomorphism : IsNearSemiringHomomorphism id
  isNearSemiringHomomorphism = record
    { +-isMonoidHomomorphism = isMonoidHomomorphism _ refl
    ; *-homo                 = λ _ _ → refl
    }

  isNearSemiringMonomorphism : IsNearSemiringMonomorphism id
  isNearSemiringMonomorphism = record
    { isNearSemiringHomomorphism = isNearSemiringHomomorphism
    ; injective = id
    }

  isNearSemiringIsomorphism : IsNearSemiringIsomorphism id
  isNearSemiringIsomorphism = record
    { isNearSemiringMonomorphism = isNearSemiringMonomorphism
    ; surjective = _, refl
    }

module _ (R : RawSemiring c ℓ) (open RawSemiring R) (refl : Reflexive _≈_) where
  open SemiringMorphisms R R

  isSemiringHomomorphism : IsSemiringHomomorphism id
  isSemiringHomomorphism = record
    { isNearSemiringHomomorphism = isNearSemiringHomomorphism _ refl
    ; 1#-homo                    = refl
    }

  isSemiringMonomorphism : IsSemiringMonomorphism id
  isSemiringMonomorphism = record
    { isSemiringHomomorphism = isSemiringHomomorphism
    ; injective = id
    }

  isSemiringIsomorphism : IsSemiringIsomorphism id
  isSemiringIsomorphism = record
    { isSemiringMonomorphism = isSemiringMonomorphism
    ; surjective = _, refl
    }

module _ (R : RawRing c ℓ) (open RawRing R) (refl : Reflexive _≈_) where
  open RingMorphisms R R

  isRingHomomorphism : IsRingHomomorphism id
  isRingHomomorphism = record
    { isSemiringHomomorphism = isSemiringHomomorphism _ refl
    ; -‿homo                 = λ _ → refl
    }

  isRingMonomorphism : IsRingMonomorphism id
  isRingMonomorphism = record
    { isRingHomomorphism = isRingHomomorphism
    ; injective = id
    }

  isRingIsomorphism : IsRingIsomorphism id
  isRingIsomorphism = record
    { isRingMonomorphism = isRingMonomorphism
    ; surjective = _, refl
    }
