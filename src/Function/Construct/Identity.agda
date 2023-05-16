------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity function
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Construct.Identity where

open import Data.Product using (_,_)
open import Function.Base using (id)
open import Function.Bundles
import Function.Definitions as Definitions
import Function.Structures as Structures
open import Level
open import Relation.Binary as B hiding (_⇔_; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; setoid)

private
  variable
    a ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- Properties

module _ (_≈_ : Rel A ℓ) where

  open Definitions _≈_ _≈_

  congruent : Congruent id
  congruent = id

  injective : Injective id
  injective = id

  surjective : Surjective id
  surjective x = x , id

  bijective : Bijective id
  bijective = injective , surjective

  inverseˡ : Inverseˡ id id
  inverseˡ x = id

  inverseʳ : Inverseʳ id id
  inverseʳ x = id

  inverseᵇ : Inverseᵇ id id
  inverseᵇ = inverseˡ , inverseʳ

------------------------------------------------------------------------
-- Structures

module _ {_≈_ : Rel A ℓ} (isEq : B.IsEquivalence _≈_) where

  open Structures _≈_ _≈_
  open B.IsEquivalence isEq

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
    ; surjective  = surjective _≈_
    }

  isBijection : IsBijection id
  isBijection = record
    { isInjection = isInjection
    ; surjective  = surjective _≈_
    }

  isLeftInverse : IsLeftInverse id id
  isLeftInverse = record
    { isCongruent = isCongruent
    ; from-cong   = id
    ; inverseˡ    = inverseˡ _≈_
    }

  isRightInverse : IsRightInverse id id
  isRightInverse = record
    { isCongruent = isCongruent
    ; from-cong   = id
    ; inverseʳ    = inverseʳ _≈_
    }

  isInverse : IsInverse id id
  isInverse = record
    { isLeftInverse = isLeftInverse
    ; inverseʳ      = inverseʳ _≈_
    }

------------------------------------------------------------------------
-- Setoid bundles

module _ (S : Setoid a ℓ) where

  open Setoid S

  function : Func S S
  function = record
    { to   = id
    ; cong = id
    }

  injection : Injection S S
  injection = record
    { to        = id
    ; cong      = id
    ; injective = injective _≈_
    }

  surjection : Surjection S S
  surjection = record
    { to         = id
    ; cong       = id
    ; surjective = surjective _≈_
    }

  bijection : Bijection S S
  bijection = record
    { to        = id
    ; cong      = id
    ; bijective = bijective _≈_
    }

  equivalence : Equivalence S S
  equivalence = record
    { to        = id
    ; from      = id
    ; to-cong   = id
    ; from-cong = id
    }

  leftInverse : LeftInverse S S
  leftInverse = record
    { to        = id
    ; from      = id
    ; to-cong   = id
    ; from-cong = id
    ; inverseˡ  = inverseˡ _≈_
    }

  rightInverse : RightInverse S S
  rightInverse = record
    { to        = id
    ; from      = id
    ; to-cong   = id
    ; from-cong = id
    ; inverseʳ  = inverseʳ _≈_
    }

  inverse : Inverse S S
  inverse = record
    { to        = id
    ; from      = id
    ; to-cong   = id
    ; from-cong = id
    ; inverse   = inverseᵇ _≈_
    }

------------------------------------------------------------------------
-- Propositional bundles

module _ (A : Set a) where

  ⟶-id : A ⟶ A
  ⟶-id = function (setoid A)

  ↣-id : A ↣ A
  ↣-id = injection (setoid A)

  ↠-id : A ↠ A
  ↠-id = surjection (setoid A)

  ⤖-id : A ⤖ A
  ⤖-id = bijection (setoid A)

  ⇔-id : A ⇔ A
  ⇔-id = equivalence (setoid A)

  ↩-id : A ↩ A
  ↩-id = leftInverse (setoid A)

  ↪-id : A ↪ A
  ↪-id = rightInverse (setoid A)

  ↔-id : A ↔ A
  ↔-id = inverse (setoid A)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version v2.0

id-⟶ = ⟶-id
{-# WARNING_ON_USAGE id-⟶
"Warning: id-⟶ was deprecated in v2.0.
Please use ⟶-id instead."
#-}

id-↣ = ↣-id
{-# WARNING_ON_USAGE id-↣
"Warning: id-↣ was deprecated in v2.0.
Please use ↣-id instead."
#-}

id-↠ = ↠-id
{-# WARNING_ON_USAGE id-↠
"Warning: id-↠ was deprecated in v2.0.
Please use ↠-id instead."
#-}

id-⤖ = ⤖-id
{-# WARNING_ON_USAGE id-⤖
"Warning: id-⤖ was deprecated in v2.0.
Please use ⤖-id instead."
#-}

id-⇔ = ⇔-id
{-# WARNING_ON_USAGE id-⇔
"Warning: id-⇔ was deprecated in v2.0.
Please use ⇔-id instead."
#-}

id-↩ = ↩-id
{-# WARNING_ON_USAGE id-↩
"Warning: id-↩ was deprecated in v2.0.
Please use ↩-id instead."
#-}

id-↪ = ↪-id
{-# WARNING_ON_USAGE id-↪
"Warning: id-↪ was deprecated in v2.0.
Please use ↪-id instead."
#-}

id-↔ = ↔-id
{-# WARNING_ON_USAGE id-↔
"Warning: id-↔ was deprecated in v2.0.
Please use ↔-id instead."
#-}
