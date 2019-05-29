------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for types of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Function.Structures
  {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
  where

open import Data.Product using (∃; _×_; _,_)
open import Function.Core
open import Function.Definitions
open import Level using (_⊔_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

------------------------------------------------------------------------
-- Definitions

record IsEqualityPreserving (f : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    cong           : Congruent _≈₁_ _≈₂_ f
    isEquivalence¹ : IsEquivalence _≈₁_
    isEquivalence² : IsEquivalence _≈₂_

  setoid¹ : Setoid a ℓ₁
  setoid¹ = record
    { isEquivalence = isEquivalence¹
    }

  setoid² : Setoid b ℓ₂
  setoid² = record
    { isEquivalence = isEquivalence²
    }


record IsInjection (f : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreserving : IsEqualityPreserving f
    injective    : Injective _≈₁_ _≈₂_ f

  open IsEqualityPreserving isPreserving public


record IsSurjection (f : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreserving : IsEqualityPreserving f
    surjective   : Surjective _≈₁_ _≈₂_ f

  open IsEqualityPreserving isPreserving public


record IsBijection (f : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isInjection : IsInjection f
    surjective  : Surjective _≈₁_ _≈₂_ f

  open IsInjection isInjection public

  bijective : Bijective _≈₁_ _≈₂_ f
  bijective = injective , surjective

  isSurjection : IsSurjection f
  isSurjection = record
    { isPreserving = isPreserving
    ; surjective   = surjective
    }


record IsLeftInverse (f : A → B) (g : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreserving : IsEqualityPreserving f
    cong²        : Congruent _≈₂_ _≈₁_ g
    inverseˡ     : LeftInverses _≈₁_ _≈₂_ f g

  open IsEqualityPreserving isPreserving public
    renaming (cong to cong¹)


record IsRightInverse (f : A → B) (g : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreserving : IsEqualityPreserving f
    cong²        : Congruent _≈₂_ _≈₁_ g
    inverseʳ     : RightInverses _≈₁_ _≈₂_ f g

  open IsEqualityPreserving isPreserving public
    renaming (cong to cong¹)


record IsInverse (f : A → B) (g : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isLeftInverse  : IsLeftInverse f g
    inverseʳ       : RightInverses _≈₁_ _≈₂_ f g

  open IsLeftInverse isLeftInverse public

  isRightInverse : IsRightInverse f g
  isRightInverse = record
    { isPreserving = isPreserving
    ; cong²        = cong²
    ; inverseʳ     = inverseʳ
    }

  inverse : Inverses _≈₁_ _≈₂_ f g
  inverse = inverseˡ , inverseʳ

