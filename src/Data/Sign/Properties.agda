------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about signs
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Sign.Properties where

open import Algebra.Bundles
open import Data.Empty
open import Data.Sign.Base
open import Data.Product using (_,_)
open import Function.Base using (_$_; id)
open import Function.Definitions using (Injective)
open import Level using (0ℓ)
open import Relation.Binary
  using (Decidable; DecidableEquality; Setoid; DecSetoid; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes; no)

open import Algebra.Structures {A = Sign} _≡_
open import Algebra.Definitions {A = Sign} _≡_
open import Algebra.Consequences.Propositional
  using (selfInverse⇒involutive; selfInverse⇒injective)

------------------------------------------------------------------------
-- Equality

infix 4 _≟_

_≟_ : DecidableEquality Sign
- ≟ - = yes refl
- ≟ + = no λ()
+ ≟ - = no λ()
+ ≟ + = yes refl

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid Sign

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≟_

≡-isDecEquivalence : IsDecEquivalence _≡_
≡-isDecEquivalence = isDecEquivalence _≟_

------------------------------------------------------------------------
-- opposite

-- Algebraic properties of opposite

opposite-selfInverse : SelfInverse opposite
opposite-selfInverse { - } { + } refl = refl
opposite-selfInverse { + } { - } refl = refl

opposite-involutive : Involutive opposite
opposite-involutive = selfInverse⇒involutive opposite-selfInverse

opposite-injective : Injective _≡_ _≡_ opposite
opposite-injective = selfInverse⇒injective opposite-selfInverse


------------------------------------------------------------------------
-- other properties of opposite

s≢opposite[s] : ∀ s → s ≢ opposite s
s≢opposite[s] - ()
s≢opposite[s] + ()

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
*-cancelʳ-≡ _ - - _  = refl
*-cancelʳ-≡ _ - + eq = ⊥-elim (s≢opposite[s] _ $ sym eq)
*-cancelʳ-≡ _ + - eq = ⊥-elim (s≢opposite[s] _ eq)
*-cancelʳ-≡ _ + + _  = refl

*-cancelˡ-≡ : LeftCancellative _*_
*-cancelˡ-≡ - _ _ eq = opposite-injective eq
*-cancelˡ-≡ + _ _ eq = eq

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

*-abelianGroup : AbelianGroup 0ℓ 0ℓ
*-abelianGroup = record
  { isAbelianGroup = *-isAbelianGroup
  }

-- Other properties of _*_

s*opposite[s]≡- : ∀ s → s * opposite s ≡ -
s*opposite[s]≡- + = refl
s*opposite[s]≡- - = refl

opposite[s]*s≡- : ∀ s → opposite s * s ≡ -
opposite[s]*s≡- + = refl
opposite[s]*s≡- - = refl
