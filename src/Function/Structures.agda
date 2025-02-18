------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for types of functions
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

module Function.Structures {a b ℓ₁ ℓ₂}
  {A : Set a} (_≈₁_ : Rel A ℓ₁) -- Equality over the domain
  {B : Set b} (_≈₂_ : Rel B ℓ₂) -- Equality over the codomain
  where

open import Data.Product.Base as Product using (∃; _×_; _,_; proj₁; proj₂)
open import Function.Base
open import Function.Consequences.Setoid
  using (surjective⇒strictlySurjective; inverseˡ⇒surjective; inverseʳ⇒injective)
open import Function.Definitions
open import Level using (_⊔_)

------------------------------------------------------------------------
-- One element structures
------------------------------------------------------------------------

record IsCongruent (to : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    cong           : Congruent _≈₁_ _≈₂_ to
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


record IsInjection (to : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent : IsCongruent to
    injective   : Injective _≈₁_ _≈₂_ to

  open IsCongruent isCongruent public


record IsSurjection (to : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent : IsCongruent to
    surjective  : Surjective _≈₁_ _≈₂_ to

  open IsCongruent isCongruent public

  from : B → A
  from = proj₁ ∘ surjective

  inverseˡ : Inverseˡ _≈₁_ _≈₂_ to from
  inverseˡ {x = x} = proj₂ (surjective x)

  strictlyInverseˡ : StrictlyInverseˡ _≈₂_ to from
  strictlyInverseˡ _ = inverseˡ Eq₁.refl

  from-injective : Injective _≈₂_ _≈₁_ from
  from-injective = Eq₂.trans (Eq₂.sym (strictlyInverseˡ _)) ∘ inverseˡ

  strictlySurjective : StrictlySurjective _≈₂_ to
  strictlySurjective = surjective⇒strictlySurjective Eq₁.setoid Eq₂.setoid surjective


record IsBijection (to : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isInjection : IsInjection to
    surjective  : Surjective _≈₁_ _≈₂_ to

  open IsInjection isInjection public

  bijective : Bijective _≈₁_ _≈₂_ to
  bijective = injective , surjective

  isSurjection : IsSurjection to
  isSurjection = record
    { isCongruent = isCongruent
    ; surjective  = surjective
    }

  open IsSurjection isSurjection public
    using (from; from-injective; strictlySurjective; inverseˡ; strictlyInverseˡ)

  private
    y≈z⇒to∘from[y]≡z : ∀ {y z} → y ≈₂ z → to (from y) ≈₂ z
    y≈z⇒to∘from[y]≡z = Eq₂.trans (strictlyInverseˡ _)

  inverseʳ : Inverseʳ _≈₁_ _≈₂_ to from
  inverseʳ = injective ∘ y≈z⇒to∘from[y]≡z

  strictlyInverseʳ : StrictlyInverseʳ _≈₁_ to from
  strictlyInverseʳ = injective ∘ strictlyInverseˡ ∘ to

  from-cong : Congruent _≈₂_ _≈₁_ from
  from-cong = inverseʳ ∘ Eq₂.sym ∘ y≈z⇒to∘from[y]≡z ∘ Eq₂.sym

  from-surjective : Surjective _≈₂_ _≈₁_ from
  from-surjective = inverseˡ⇒surjective Eq₂.setoid Eq₁.setoid inverseʳ

  from-bijective : Bijective _≈₂_ _≈₁_ from
  from-bijective = from-injective , from-surjective


------------------------------------------------------------------------
-- Two element structures
------------------------------------------------------------------------

record IsLeftInverse (to : A → B) (from : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent  : IsCongruent to
    from-cong    : Congruent _≈₂_ _≈₁_ from
    inverseˡ     : Inverseˡ _≈₁_ _≈₂_ to from

  open IsCongruent isCongruent public
    renaming (cong to to-cong)

  strictlyInverseˡ : StrictlyInverseˡ _≈₂_ to from
  strictlyInverseˡ _ = inverseˡ Eq₁.refl

  surjective = inverseˡ⇒surjective Eq₁.setoid Eq₂.setoid inverseˡ

  isSurjection : IsSurjection to
  isSurjection = record
    { isCongruent = isCongruent
    ; surjective = surjective
    }


record IsRightInverse (to : A → B) (from : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent : IsCongruent to
    from-cong   : Congruent _≈₂_ _≈₁_ from
    inverseʳ    : Inverseʳ _≈₁_ _≈₂_ to from

  open IsCongruent isCongruent public
    renaming (cong to to-cong)

  strictlyInverseʳ : StrictlyInverseʳ _≈₁_ to from
  strictlyInverseʳ _ = inverseʳ Eq₂.refl

  injective : Injective _≈₁_ _≈₂_ to
  injective = inverseʳ⇒injective Eq₁.setoid Eq₂.setoid to inverseʳ

  isInjection : IsInjection to
  isInjection = record
    { isCongruent = isCongruent
    ; injective   = injective
    }


record IsInverse (to : A → B) (from : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isLeftInverse : IsLeftInverse to from
    inverseʳ      : Inverseʳ _≈₁_ _≈₂_ to from

  open IsLeftInverse isLeftInverse public

  isRightInverse : IsRightInverse to from
  isRightInverse = record
    { isCongruent = isCongruent
    ; from-cong   = from-cong
    ; inverseʳ    = inverseʳ
    }

  open IsRightInverse isRightInverse public
    using (strictlyInverseʳ)

  inverse : Inverseᵇ _≈₁_ _≈₂_ to from
  inverse = inverseˡ , inverseʳ


------------------------------------------------------------------------
-- Three element structures
------------------------------------------------------------------------

record IsBiEquivalence
  (to : A → B) (from₁ : B → A) (from₂ : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    to-isCongruent : IsCongruent to
    from₁-cong    : Congruent _≈₂_ _≈₁_ from₁
    from₂-cong    : Congruent _≈₂_ _≈₁_ from₂

  open IsCongruent to-isCongruent public
    renaming (cong to to-cong₁)


record IsBiInverse
  (to : A → B) (from₁ : B → A) (from₂ : B → A) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    to-isCongruent : IsCongruent to
    from₁-cong     : Congruent _≈₂_ _≈₁_ from₁
    from₂-cong     : Congruent _≈₂_ _≈₁_ from₂
    inverseˡ       : Inverseˡ _≈₁_ _≈₂_ to from₁
    inverseʳ       : Inverseʳ _≈₁_ _≈₂_ to from₂

  open IsCongruent to-isCongruent public
    renaming (cong to to-cong)


------------------------------------------------------------------------
-- Other
------------------------------------------------------------------------

-- See the comment on `SplitSurjection` in `Function.Bundles` for an
-- explanation of (split) surjections.
record IsSplitSurjection (to : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    from : B → A
    isLeftInverse : IsLeftInverse to from

  open IsLeftInverse isLeftInverse public
