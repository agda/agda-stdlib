------------------------------------------------------------------------
-- The Agda standard library
--
-- Ways to give instances of certain structures where some fields can
-- be given in terms of others.
-- The contents of this file should usually be accessed from `Function`.
------------------------------------------------------------------------


{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)


module Function.Structures.Biased {a b ℓ₁ ℓ₂}
  {A : Set a} (_≈₁_ : Rel A ℓ₁) -- Equality over the domain
  {B : Set b} (_≈₂_ : Rel B ℓ₂) -- Equality over the codomain
  where

open import Data.Product.Base as Product using (∃; _×_; _,_)
open import Function.Base using (_∘_; id)
open import Function.Definitions
  using (StrictlySurjective; StrictlyInverseˡ; StrictlyInverseʳ; Congruent)
open import Function.Consequences.Setoid
  using (strictlySurjective⇒surjective; strictlyInverseˡ⇒inverseˡ
        ; strictlyInverseʳ⇒inverseʳ)
open import Level using (_⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open import Function.Structures _≈₁_ _≈₂_

------------------------------------------------------------------------
-- Surjection
------------------------------------------------------------------------

record IsStrictSurjection (f : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent : IsCongruent f
    strictlySurjective : StrictlySurjective _≈₂_ f

  open IsCongruent isCongruent public

  isSurjection : IsSurjection f
  isSurjection = record
    { isCongruent = isCongruent
    ; surjective = strictlySurjective⇒surjective
        Eq₁.setoid Eq₂.setoid cong strictlySurjective
    }

open IsStrictSurjection public
  using () renaming (isSurjection to isStrictSurjection)

------------------------------------------------------------------------
-- Bijection
------------------------------------------------------------------------

record IsStrictBijection (f : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isInjection : IsInjection f
    strictlySurjective  : StrictlySurjective _≈₂_ f

  isBijection : IsBijection f
  isBijection = record
    { isInjection = isInjection
    ; surjective = strictlySurjective⇒surjective
        Eq₁.setoid Eq₂.setoid cong strictlySurjective
    } where open IsInjection isInjection

open IsStrictBijection public
  using () renaming (isBijection to isStrictBijection)

------------------------------------------------------------------------
-- Left inverse
------------------------------------------------------------------------

record IsStrictLeftInverse (to : A → B) (from : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent  : IsCongruent to
    from-cong    : Congruent _≈₂_ _≈₁_ from
    strictlyInverseˡ : StrictlyInverseˡ _≈₂_ to from

  isLeftInverse : IsLeftInverse to from
  isLeftInverse = record
    { isCongruent = isCongruent
    ; from-cong = from-cong
    ; inverseˡ = strictlyInverseˡ⇒inverseˡ
        Eq₁.setoid Eq₂.setoid cong strictlyInverseˡ
    } where open IsCongruent isCongruent

open IsStrictLeftInverse public
  using () renaming (isLeftInverse to isStrictLeftInverse)

------------------------------------------------------------------------
-- Right inverse
------------------------------------------------------------------------

record IsStrictRightInverse (to : A → B) (from : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent : IsCongruent to
    from-cong   : Congruent _≈₂_ _≈₁_ from
    strictlyInverseʳ : StrictlyInverseʳ _≈₁_ to from

  isRightInverse : IsRightInverse to from
  isRightInverse = record
    { isCongruent = isCongruent
    ; from-cong = from-cong
    ; inverseʳ = strictlyInverseʳ⇒inverseʳ
        Eq₁.setoid Eq₂.setoid from-cong strictlyInverseʳ
    } where open IsCongruent isCongruent

open IsStrictRightInverse public
  using () renaming (isRightInverse to isStrictRightInverse)

------------------------------------------------------------------------
-- Inverse
------------------------------------------------------------------------

record IsStrictInverse (to : A → B) (from : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isLeftInverse : IsLeftInverse to from
    strictlyInverseʳ : StrictlyInverseʳ _≈₁_ to from

  isInverse : IsInverse to from
  isInverse = record
    { isLeftInverse = isLeftInverse
    ; inverseʳ      = strictlyInverseʳ⇒inverseʳ
        Eq₁.setoid Eq₂.setoid from-cong strictlyInverseʳ
    } where open IsLeftInverse isLeftInverse

open IsStrictInverse public
  using () renaming (isInverse to isStrictInverse)
