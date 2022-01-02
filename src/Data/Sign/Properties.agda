------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about signs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sign.Properties where

open import Algebra.Bundles
open import Data.Empty
open import Data.Sign.Base
open import Data.Product using (_,_)
open import Function hiding (Inverse)
open import Level using (0ℓ)
open import Relation.Binary using (Decidable; Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

open import Algebra.Structures {A = Sign} _≡_
open import Algebra.Definitions {A = Sign} _≡_

------------------------------------------------------------------------
-- Equality

infix 4 _≟_

_≟_ : Decidable {A = Sign} _≡_
- ≟ - = yes refl
- ≟ + = no λ()
+ ≟ - = no λ()
+ ≟ + = yes refl

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid Sign

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≟_

------------------------------------------------------------------------
-- opposite

s≢opposite[s] : ∀ s → s ≢ opposite s
s≢opposite[s] - ()
s≢opposite[s] + ()

opposite-injective : ∀ {s t} → opposite s ≡ opposite t → s ≡ t
opposite-injective { - } { - } refl = refl
opposite-injective { + } { + } refl = refl

------------------------------------------------------------------------
-- _*_

-- Algebraic properties of _*_

s*s≡+ : ∀ s → s * s ≡ +
s*s≡+ + = refl
s*s≡+ - = refl

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

*-inverse : Inverse + id _*_
*-inverse = s*s≡+ , s*s≡+

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

*-isCommutativeSemigroup : IsCommutativeSemigroup _*_
*-isCommutativeSemigroup = record
  { isSemigroup = *-isSemigroup
  ; comm = *-comm
  }

*-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
*-commutativeSemigroup = record
  { isCommutativeSemigroup = *-isCommutativeSemigroup
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

*-isCommutativeMonoid : IsCommutativeMonoid _*_ +
*-isCommutativeMonoid = record
   { isMonoid = *-isMonoid
   ; comm = *-comm
   }

*-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-commutativeMonoid = record
  { isCommutativeMonoid = *-isCommutativeMonoid
  }

*-isGroup : IsGroup _*_ + id
*-isGroup = record
  { isMonoid = *-isMonoid
  ; inverse = *-inverse
  ; ⁻¹-cong = id
  }

*-group : Group 0ℓ 0ℓ
*-group = record
  { isGroup = *-isGroup
  }

*-isAbelianGroup : IsAbelianGroup _*_ + id
*-isAbelianGroup = record
  { isGroup = *-isGroup
  ; comm = *-comm
  }

-- Other properties of _*_

s*opposite[s]≡- : ∀ s → s * opposite s ≡ -
s*opposite[s]≡- + = refl
s*opposite[s]≡- - = refl

opposite[s]*s≡- : ∀ s → opposite s * s ≡ -
opposite[s]*s≡- + = refl
opposite[s]*s≡- - = refl
