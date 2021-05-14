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
        ; module LatticeMorphisms
        )
open import Data.Product using (_,_)
open import Function.Base using (id)
open import Level using (Level)
open import Relation.Binary.Morphism.Construct.Identity using (isRelHomomorphism)

private
  variable
    c ℓ : Level

module _ (M : Magma c ℓ) where
  open Magma M
  open MagmaMorphisms rawMagma rawMagma

  isMagmaHomomorphism : IsMagmaHomomorphism id
  isMagmaHomomorphism = record
    { isRelHomomorphism = isRelHomomorphism _≈_
    ; homo = λ _ _ → refl
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

module _ (M : Monoid c ℓ) where
  open Monoid M
  open MonoidMorphisms rawMonoid rawMonoid

  isMonoidHomomorphism : IsMonoidHomomorphism id
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = isMagmaHomomorphism magma
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

module _ (G : Group c ℓ) where
  open Group G
  open GroupMorphisms rawGroup rawGroup

  isGroupHomomorphism : IsGroupHomomorphism id
  isGroupHomomorphism = record
    { isMonoidHomomorphism = isMonoidHomomorphism monoid
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

module _ (R : NearSemiring c ℓ) where
  open NearSemiring R
  open NearSemiringMorphisms rawNearSemiring rawNearSemiring

  isNearSemiringHomomorphism : IsNearSemiringHomomorphism id
  isNearSemiringHomomorphism = record
    { +-isMonoidHomomorphism = isMonoidHomomorphism +-monoid
    ; *-isMagmaHomomorphism = isMagmaHomomorphism *-magma
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

module _ (R : Semiring c ℓ) where
  open Semiring R
  open SemiringMorphisms rawSemiring rawSemiring

  isSemiringHomomorphism : IsSemiringHomomorphism id
  isSemiringHomomorphism = record
    { +-isMonoidHomomorphism = isMonoidHomomorphism +-monoid
    ; *-isMonoidHomomorphism = isMonoidHomomorphism *-monoid
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

module _ (R : Ring c ℓ) where
  open Ring R
  open RingMorphisms rawRing rawRing

  isRingHomomorphism : IsRingHomomorphism id
  isRingHomomorphism = record
    { +-isGroupHomomorphism = isGroupHomomorphism +-group
    ; *-isMonoidHomomorphism = isMonoidHomomorphism *-monoid
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

module _ (R : Lattice c ℓ) where
  open Lattice R
  open LatticeMorphisms rawLattice rawLattice

  isLatticeHomomorphism : IsLatticeHomomorphism id
  isLatticeHomomorphism = record
    { ∧-isMagmaHomomorphism = isMagmaHomomorphism ∧-magma
    ; ∨-isMagmaHomomorphism = isMagmaHomomorphism ∨-magma
    }

  isLatticeMonomorphism : IsLatticeMonomorphism id
  isLatticeMonomorphism = record
    { isLatticeHomomorphism = isLatticeHomomorphism
    ; injective = id
    }

  isLatticeIsomorphism : IsLatticeIsomorphism id
  isLatticeIsomorphism = record
    { isLatticeMonomorphism = isLatticeMonomorphism
    ; surjective = _, refl
    }
