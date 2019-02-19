------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about signs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sign.Properties where

open import Algebra
open import Data.Empty
open import Data.Sign
open import Data.Product using (_,_)
open import Function
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import Algebra.Structures {A = Sign} _≡_
open import Algebra.FunctionProperties {A = Sign} _≡_

-- The opposite of a sign is not equal to the sign.

s≢opposite[s] : ∀ s → s ≢ opposite s
s≢opposite[s] - ()
s≢opposite[s] + ()

opposite-injective : ∀ {s t} → opposite s ≡ opposite t → s ≡ t
opposite-injective { - } { - } refl = refl
opposite-injective { - } { + } ()
opposite-injective { + } { - } ()
opposite-injective { + } { + } refl = refl

------------------------------------------------------------------------
-- _*_

-- Algebraic properties of _*_

*-identityˡ : LeftIdentity + _*_
*-identityˡ _ = refl

*-identityʳ : RightIdentity + _*_
*-identityʳ - = refl
*-identityʳ + = refl

*-identity : Identity + _*_
*-identity = *-identityˡ  , *-identityʳ

*-comm : Commutative _*_
*-comm + + = refl
*-comm + - = refl
*-comm - + = refl
*-comm - - = refl

*-assoc : Associative _*_
*-assoc + + _ = refl
*-assoc + - _ = refl
*-assoc - + _ = refl
*-assoc - - + = refl
*-assoc - - - = refl

*-cancelʳ-≡ : RightCancellative _*_
*-cancelʳ-≡ - - _  = refl
*-cancelʳ-≡ - + eq = ⊥-elim (s≢opposite[s] _ $ sym eq)
*-cancelʳ-≡ + - eq = ⊥-elim (s≢opposite[s] _ eq)
*-cancelʳ-≡ + + _  = refl

*-cancelˡ-≡ : LeftCancellative _*_
*-cancelˡ-≡ - eq = opposite-injective eq
*-cancelˡ-≡ + eq = eq

*-cancel-≡ : Cancellative _*_
*-cancel-≡ = *-cancelˡ-≡ , *-cancelʳ-≡

*-isMagma : IsMagma _*_
*-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _*_
  }

*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = *-assoc
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-isMonoid : IsMonoid _*_ +
*-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-monoid : Monoid 0ℓ 0ℓ
*-monoid = record
  { isMonoid = *-isMonoid
  }

-- Other properties of _*_

s*s≡+ : ∀ s → s * s ≡ +
s*s≡+ + = refl
s*s≡+ - = refl

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

opposite-not-equal = s≢opposite[s]
{-# WARNING_ON_USAGE opposite-not-equal
"Warning: opposite-not-equal was deprecated in v0.15.
Please use s≢opposite[s] instead."
#-}
opposite-cong = opposite-injective
{-# WARNING_ON_USAGE opposite-cong
"Warning: opposite-cong was deprecated in v0.15.
Please use opposite-injective instead."
#-}
cancel-*-left = *-cancelˡ-≡
{-# WARNING_ON_USAGE cancel-*-left
"Warning: cancel-*-left was deprecated in v0.15.
Please use *-cancelˡ-≡ instead."
#-}
cancel-*-right = *-cancelʳ-≡
{-# WARNING_ON_USAGE cancel-*-right
"Warning: cancel-*-right was deprecated in v0.15.
Please use *-cancelʳ-≡ instead."
#-}
*-cancellative = *-cancel-≡
{-# WARNING_ON_USAGE *-cancellative
"Warning: *-cancellative was deprecated in v0.15.
Please use *-cancel-≡ instead."
#-}
