------------------------------------------------------------------------
-- The Agda standard library
--
-- The `IsMagma` and related algebraic structures
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`, unless
-- you want to parameterise it via the equality relation.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

module Algebra.Structures.IsMagma
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions _≈_
import Algebra.Consequences.Setoid as Consequences
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Structures with 1 binary operation
------------------------------------------------------------------------

record IsMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_
    ∙-cong        : Congruent₂ ∙

  open IsEquivalence isEquivalence public

  setoid : Setoid a ℓ
  setoid = record { isEquivalence = isEquivalence }

  open Consequences.Congruence setoid ∙-cong public

record IsCommutativeMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    comm    : Commutative ∙

  open IsMagma isMagma public

record IsIdempotentMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    idem    : Idempotent ∙

  open IsMagma isMagma public

record IsAlternativeMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙
    alter    : Alternative ∙

  open IsMagma isMagma public

  alternativeˡ : LeftAlternative ∙
  alternativeˡ = proj₁ alter

  alternativeʳ : RightAlternative ∙
  alternativeʳ = proj₂ alter

record IsFlexibleMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙
    flex     : Flexible ∙

  open IsMagma isMagma public

record IsMedialMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    medial  : Medial ∙

  open IsMagma isMagma public

record IsSemimedialMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma    : IsMagma ∙
    semiMedial : Semimedial ∙

  open IsMagma isMagma public

  semimedialˡ : LeftSemimedial ∙
  semimedialˡ = proj₁ semiMedial

  semimedialʳ : RightSemimedial ∙
  semimedialʳ = proj₂ semiMedial

record IsSelectiveMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    sel     : Selective ∙

  open IsMagma isMagma public

record IsUnitalMagma (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙
    identity : Identity ε ∙

  open IsMagma isMagma public

  identityˡ : LeftIdentity ε ∙
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε ∙
  identityʳ = proj₂ identity

record IsInvertibleMagma (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma _∙_
    inverse   : Inverse ε _⁻¹ _∙_
    ⁻¹-cong   : Congruent₁ _⁻¹

  open IsMagma isMagma public

  inverseˡ : LeftInverse ε _⁻¹ _∙_
  inverseˡ = proj₁ inverse

  inverseʳ : RightInverse ε _⁻¹ _∙_
  inverseʳ = proj₂ inverse

record IsInvertibleUnitalMagma (_∙_ : Op₂ A) (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isInvertibleMagma : IsInvertibleMagma _∙_  ε ⁻¹
    identity          : Identity ε _∙_

  open IsInvertibleMagma isInvertibleMagma public

  identityˡ : LeftIdentity ε _∙_
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε _∙_
  identityʳ = proj₂ identity

  isUnitalMagma : IsUnitalMagma _∙_  ε
  isUnitalMagma = record
    { isMagma  = isMagma
    ; identity = identity
    }
