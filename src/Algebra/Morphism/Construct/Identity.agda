------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity morphism for algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Algebra.Morphism.Construct.Identity where

open import Algebra.Bundles
open import Algebra.Morphism.Structures
  using ( module MagmaMorphisms
        ; module MonoidMorphisms
        ; module GroupMorphisms
        ; module NearSemiringMorphisms
        ; module SemiringMorphisms
        ; module RingWithoutOneMorphisms
        ; module RingMorphisms
        ; module QuasigroupMorphisms
        ; module LoopMorphisms
        ; module KleeneAlgebraMorphisms
        )
open import Data.Product.Base using (_,_)
open import Function.Base using (id)
import Function.Construct.Identity as Id
open import Level using (Level)
open import Relation.Binary.Morphism.Construct.Identity using (isRelHomomorphism)
open import Relation.Binary.Definitions using (Reflexive)

private
  variable
    c ℓ : Level

------------------------------------------------------------------------
-- Magmas

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
    ; surjective = Id.surjective _
    }

------------------------------------------------------------------------
-- Monoids

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
    ; surjective = Id.surjective _
    }

------------------------------------------------------------------------
-- Groups

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
    ; surjective = Id.surjective _
    }

------------------------------------------------------------------------
-- Near semirings

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
    ; surjective = Id.surjective _
    }

------------------------------------------------------------------------
-- Semirings

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
    ; surjective = Id.surjective _
    }

------------------------------------------------------------------------
-- RingWithoutOne

module _ (R : RawRingWithoutOne c ℓ) (open RawRingWithoutOne R) (refl : Reflexive _≈_) where
  open RingWithoutOneMorphisms R R

  isRingWithoutOneHomomorphism : IsRingWithoutOneHomomorphism id
  isRingWithoutOneHomomorphism = record
    { +-isGroupHomomorphism  = isGroupHomomorphism _ refl
    ; *-homo                 = λ _ _ → refl
    }

  isRingWithoutOneMonomorphism : IsRingWithoutOneMonomorphism id
  isRingWithoutOneMonomorphism = record
    { isRingWithoutOneHomomorphism = isRingWithoutOneHomomorphism
    ; injective = id
    }

  isRingWithoutOneIsoMorphism : IsRingWithoutOneIsoMorphism id
  isRingWithoutOneIsoMorphism = record
    { isRingWithoutOneMonomorphism = isRingWithoutOneMonomorphism
    ; surjective = Id.surjective _
    }

------------------------------------------------------------------------
-- Rings

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
    ; surjective = Id.surjective _
    }

------------------------------------------------------------------------
-- Quasigroup

module _ (Q : RawQuasigroup c ℓ) (open RawQuasigroup Q) (refl : Reflexive _≈_) where
  open QuasigroupMorphisms Q Q

  isQuasigroupHomomorphism : IsQuasigroupHomomorphism id
  isQuasigroupHomomorphism = record
    { isRelHomomorphism = isRelHomomorphism _
    ; ∙-homo            = λ _ _ → refl
    ; \\-homo            = λ _ _ → refl
    ; //-homo            = λ _ _ → refl
    }

  isQuasigroupMonomorphism : IsQuasigroupMonomorphism id
  isQuasigroupMonomorphism = record
    { isQuasigroupHomomorphism = isQuasigroupHomomorphism
    ; injective = id
    }

  isQuasigroupIsomorphism : IsQuasigroupIsomorphism id
  isQuasigroupIsomorphism = record
    { isQuasigroupMonomorphism = isQuasigroupMonomorphism
    ; surjective = Id.surjective _
    }

------------------------------------------------------------------------
-- Loop

module _ (L : RawLoop c ℓ) (open RawLoop L) (refl : Reflexive _≈_) where
  open LoopMorphisms L L

  isLoopHomomorphism : IsLoopHomomorphism id
  isLoopHomomorphism = record
    { isQuasigroupHomomorphism = isQuasigroupHomomorphism _ refl
    ; ε-homo = refl
    }

  isLoopMonomorphism : IsLoopMonomorphism id
  isLoopMonomorphism = record
    { isLoopHomomorphism = isLoopHomomorphism
    ; injective = id
    }

  isLoopIsomorphism : IsLoopIsomorphism id
  isLoopIsomorphism = record
    { isLoopMonomorphism = isLoopMonomorphism
    ; surjective = Id.surjective _
    }

------------------------------------------------------------------------
-- KleeneAlgebra

module _ (K : RawKleeneAlgebra c ℓ) (open RawKleeneAlgebra K) (refl : Reflexive _≈_) where
  open KleeneAlgebraMorphisms K K

  isKleeneAlgebraHomomorphism : IsKleeneAlgebraHomomorphism id
  isKleeneAlgebraHomomorphism = record
    { isSemiringHomomorphism = isSemiringHomomorphism _ refl
    ; ⋆-homo = λ _ → refl
    }

  isKleeneAlgebraMonomorphism : IsKleeneAlgebraMonomorphism id
  isKleeneAlgebraMonomorphism = record
    { isKleeneAlgebraHomomorphism = isKleeneAlgebraHomomorphism
    ; injective = id
    }

  isKleeneAlgebraIsomorphism : IsKleeneAlgebraIsomorphism id
  isKleeneAlgebraIsomorphism = record
    { isKleeneAlgebraMonomorphism = isKleeneAlgebraMonomorphism
    ; surjective = Id.surjective _
    }

