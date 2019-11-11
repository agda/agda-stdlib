------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity function
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Construct.Identity where

open import Data.Product using (_,_)
open import Function using (id)
open import Function.Bundles
import Function.Definitions as Definitions
import Function.Structures as Structures
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; setoid)

private
  variable
    a ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- Properties

module _ (_≈_ : Rel A ℓ) where

  open Definitions _≈_ _≈_

  injective : Injective id
  injective = id

  surjective : Reflexive _≈_ → Surjective id
  surjective refl x = x , refl

  bijective : Reflexive _≈_ → Bijective id
  bijective refl = injective , surjective refl

  inverseˡ : Reflexive _≈_ → Inverseˡ id id
  inverseˡ refl x = refl

  inverseʳ : Reflexive _≈_ → Inverseʳ id id
  inverseʳ refl x = refl

  inverseᵇ : Reflexive _≈_ → Inverseᵇ id id
  inverseᵇ refl = inverseˡ refl , inverseʳ refl

------------------------------------------------------------------------
-- Structures

module _ {_≈_ : Rel A ℓ} (isEq : IsEquivalence _≈_) where

  open Structures _≈_ _≈_
  open IsEquivalence isEq

  isCongruent : IsCongruent id
  isCongruent = record
    { cong           = id
    ; isEquivalence₁ = isEq
    ; isEquivalence₂ = isEq
    }

  isInjection : IsInjection id
  isInjection = record
    { isCongruent = isCongruent
    ; injective   = injective _≈_
    }

  isSurjection : IsSurjection id
  isSurjection = record
    { isCongruent = isCongruent
    ; surjective  = surjective _≈_ refl
    }

  isBijection : IsBijection id
  isBijection = record
    { isInjection = isInjection
    ; surjective  = surjective _≈_ refl
    }

  isLeftInverse : IsLeftInverse id id
  isLeftInverse = record
    { isCongruent = isCongruent
    ; cong₂       = id
    ; inverseˡ    = inverseˡ _≈_ refl
    }

  isRightInverse : IsRightInverse id id
  isRightInverse = record
    { isCongruent = isCongruent
    ; cong₂       = id
    ; inverseʳ    = inverseʳ _≈_ refl
    }

  isInverse : IsInverse id id
  isInverse = record
    { isLeftInverse = isLeftInverse
    ; inverseʳ      = inverseʳ _≈_ refl
    }

------------------------------------------------------------------------
-- Setoid bundles

module _ (S : Setoid a ℓ) where

  open Setoid S

  injection : Injection S S
  injection = record
    { f         = id
    ; cong      = id
    ; injective = injective _≈_
    }

  surjection : Surjection S S
  surjection = record
    { f          = id
    ; cong       = id
    ; surjective = surjective _≈_ refl
    }

  bijection : Bijection S S
  bijection = record
    { f         = id
    ; cong      = id
    ; bijective = bijective _≈_ refl
    }

  equivalence : Equivalence S S
  equivalence = record
    { f     = id
    ; g     = id
    ; cong₁ = id
    ; cong₂ = id
    }

  leftInverse : LeftInverse S S
  leftInverse = record
    { f        = id
    ; g        = id
    ; cong₁    = id
    ; cong₂    = id
    ; inverseˡ = inverseˡ _≈_ refl
    }

  rightInverse : RightInverse S S
  rightInverse = record
    { f        = id
    ; g        = id
    ; cong₁    = id
    ; cong₂    = id
    ; inverseʳ = inverseʳ _≈_ refl
    }

  inverse : Inverse S S
  inverse = record
    { f       = id
    ; f⁻¹     = id
    ; cong₁   = id
    ; cong₂   = id
    ; inverse = inverseᵇ _≈_ refl
    }

------------------------------------------------------------------------
-- Propositional bundles

module _ (A : Set a) where

  id-↣ : A ↣ A
  id-↣ = injection (setoid A)

  id-↠ : A ↠ A
  id-↠ = surjection (setoid A)

  id-⤖ : A ⤖ A
  id-⤖ = bijection (setoid A)

  id-⇔ : A ⇔ A
  id-⇔ = equivalence (setoid A)

  id-↩ : A ↩ A
  id-↩ = leftInverse (setoid A)

  id-↪ : A ↪ A
  id-↪ = rightInverse (setoid A)

  id-↔ : A ↔ A
  id-↔ = inverse (setoid A)
