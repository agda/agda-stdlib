------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for types of functions
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Function.Structures
  {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
  where

open import Data.Product using (∃; _×_; _,_)
open import Function.Base
open import Function.Definitions
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Definitions

record IsCongruent (f : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    cong           : Congruent _≈₁_ _≈₂_ f
    isEquivalence₁ : IsEquivalence _≈₁_
    isEquivalence₂ : IsEquivalence _≈₂_

  module Eq₁ where

    setoid : Setoid a ℓ₁
    setoid = record
      { isEquivalence = isEquivalence₁
      }

    open Setoid setoid public

  module Eq₂ where

    setoid : Setoid b ℓ₂
    setoid = record
      { isEquivalence = isEquivalence₂
      }

    open Setoid setoid public


record IsInjection (f : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent : IsCongruent f
    injective   : Injective _≈₁_ _≈₂_ f

  open IsCongruent isCongruent public


record IsSurjection (f : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent : IsCongruent f
    surjective  : Surjective _≈₁_ _≈₂_ f

  open IsCongruent isCongruent public


record IsBijection (f : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isInjection : IsInjection f
    surjective  : Surjective _≈₁_ _≈₂_ f

  open IsInjection isInjection public

  bijective : Bijective _≈₁_ _≈₂_ f
  bijective = injective , surjective

  isSurjection : IsSurjection f
  isSurjection = record
    { isCongruent = isCongruent
    ; surjective  = surjective
    }


record IsLeftInverse (f : A → B) (g : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent  : IsCongruent f
    cong₂        : Congruent _≈₂_ _≈₁_ g
    inverseˡ     : Inverseˡ _≈₁_ _≈₂_ f g

  open IsCongruent isCongruent public
    renaming (cong to cong₁)


record IsRightInverse (f : A → B) (g : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent : IsCongruent f
    cong₂       : Congruent _≈₂_ _≈₁_ g
    inverseʳ    : Inverseʳ _≈₁_ _≈₂_ f g

  open IsCongruent isCongruent public
    renaming (cong to cong₁)

record IsBiEquivalence
  (f : A → B) (g₁ : B → A) (g₂ : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    f-isCongruent : IsCongruent f
    cong₂         : Congruent _≈₂_ _≈₁_ g₁
    cong₃         : Congruent _≈₂_ _≈₁_ g₂

  open IsCongruent f-isCongruent public
    renaming (cong to cong₁)

record IsBiInverse
  (f : A → B) (g₁ : B → A) (g₂ : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    f-isCongruent : IsCongruent f
    cong₂         : Congruent _≈₂_ _≈₁_ g₁
    inverseˡ      : Inverseˡ _≈₁_ _≈₂_ f g₁
    cong₃         : Congruent _≈₂_ _≈₁_ g₂
    inverseʳ      : Inverseʳ _≈₁_ _≈₂_ f g₂

  open IsCongruent f-isCongruent public
    renaming (cong to cong₁)


record IsInverse (f : A → B) (g : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isLeftInverse : IsLeftInverse f g
    inverseʳ      : Inverseʳ _≈₁_ _≈₂_ f g

  open IsLeftInverse isLeftInverse public

  isRightInverse : IsRightInverse f g
  isRightInverse = record
    { isCongruent = isCongruent
    ; cong₂       = cong₂
    ; inverseʳ    = inverseʳ
    }

  inverse : Inverseᵇ _≈₁_ _≈₂_ f g
  inverse = inverseˡ , inverseʳ
