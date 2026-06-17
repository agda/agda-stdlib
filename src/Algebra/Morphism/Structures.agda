------------------------------------------------------------------------
-- The Agda standard library
--
-- Morphisms between algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Morphism.Structures where

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Bundles
import Algebra.Morphism.Definitions as MorphismDefinitions
open import Level using (Level; _⊔_)
open import Function.Definitions using (Injective; Surjective)
open import Relation.Binary.Morphism.Structures
  using (IsRelHomomorphism; IsRelMonomorphism; IsRelIsomorphism)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Morphisms over SuccessorSet-like structures
------------------------------------------------------------------------

module SuccessorSetMorphisms
  (N₁ : RawSuccessorSet a ℓ₁) (N₂ : RawSuccessorSet b ℓ₂)
  where

  open RawSuccessorSet N₁
    renaming (Carrier to A; _≈_ to _≈₁_; suc# to suc#₁; zero# to zero#₁)
  open RawSuccessorSet N₂
    renaming (Carrier to B; _≈_ to _≈₂_; suc# to suc#₂; zero# to zero#₂)
  open MorphismDefinitions A B _≈₂_


  record IsSuccessorSetHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      suc#-homo         : Homomorphic₁ ⟦_⟧ suc#₁ suc#₂
      zero#-homo        : Homomorphic₀ ⟦_⟧ zero#₁ zero#₂

  record IsSuccessorSetMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isSuccessorSetHomomorphism : IsSuccessorSetHomomorphism ⟦_⟧
      injective                  : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsSuccessorSetHomomorphism isSuccessorSetHomomorphism public

    isRelMonomorphism : IsRelMonomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelMonomorphism = record
      { isHomomorphism = isRelHomomorphism
      ; injective      = injective
      }


  record IsSuccessorSetIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isSuccessorSetMonomorphism : IsSuccessorSetMonomorphism ⟦_⟧
      surjective                 : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsSuccessorSetMonomorphism isSuccessorSetMonomorphism public

    isRelIsomorphism : IsRelIsomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelIsomorphism = record
      { isMonomorphism = isRelMonomorphism
      ; surjective     = surjective
      }


------------------------------------------------------------------------
-- Morphisms over magma-like structures
------------------------------------------------------------------------

module MagmaMorphisms (M₁ : RawMagma a ℓ₁) (M₂ : RawMagma b ℓ₂) where

  open RawMagma M₁ renaming (Carrier to A; _≈_ to _≈₁_; _∙_ to _∙_)
  open RawMagma M₂ renaming (Carrier to B; _≈_ to _≈₂_; _∙_ to _◦_)
  open MorphismDefinitions A B _≈₂_


  record IsMagmaHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      ∙-homo            : Homomorphic₂ ⟦_⟧ _∙_ _◦_

    -- Deprecated.
    homo = ∙-homo
    {-# WARNING_ON_USAGE homo
    "Warning: homo was deprecated in v3.0.
    Please use ∙-homo instead. "
    #-}

    open IsRelHomomorphism isRelHomomorphism public
      renaming (cong to ⟦⟧-cong)


  record IsMagmaMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMagmaHomomorphism : IsMagmaHomomorphism ⟦_⟧
      injective           : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsMagmaHomomorphism isMagmaHomomorphism public

    isRelMonomorphism : IsRelMonomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelMonomorphism = record
      { isHomomorphism = isRelHomomorphism
      ; injective      = injective
      }


  record IsMagmaIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMagmaMonomorphism : IsMagmaMonomorphism ⟦_⟧
      surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsMagmaMonomorphism isMagmaMonomorphism public

    isRelIsomorphism : IsRelIsomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelIsomorphism = record
      { isMonomorphism = isRelMonomorphism
      ; surjective     = surjective
      }


------------------------------------------------------------------------
-- Morphisms over monoid-like structures
------------------------------------------------------------------------

module MonoidMorphisms (M₁ : RawMonoid a ℓ₁) (M₂ : RawMonoid b ℓ₂) where

  open RawMonoid M₁ renaming (Carrier to A; _≈_ to _≈₁_; _∙_ to _∙_; ε to ε₁)
  open RawMonoid M₂ renaming (Carrier to B; _≈_ to _≈₂_; _∙_ to _◦_; ε to ε₂)
  open MorphismDefinitions A B _≈₂_
  open MagmaMorphisms (RawMonoid.rawMagma M₁) (RawMonoid.rawMagma M₂)


  record IsMonoidHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMagmaHomomorphism : IsMagmaHomomorphism ⟦_⟧
      ε-homo              : Homomorphic₀ ⟦_⟧ ε₁ ε₂

    open IsMagmaHomomorphism isMagmaHomomorphism public


  record IsMonoidMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧
      injective            : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsMonoidHomomorphism isMonoidHomomorphism public

    isMagmaMonomorphism : IsMagmaMonomorphism ⟦_⟧
    isMagmaMonomorphism = record
      { isMagmaHomomorphism = isMagmaHomomorphism
      ; injective           = injective
      }

    open IsMagmaMonomorphism isMagmaMonomorphism public
      using (isRelMonomorphism)


  record IsMonoidIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMonoidMonomorphism : IsMonoidMonomorphism ⟦_⟧
      surjective           : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsMonoidMonomorphism isMonoidMonomorphism public

    isMagmaIsomorphism : IsMagmaIsomorphism ⟦_⟧
    isMagmaIsomorphism = record
      { isMagmaMonomorphism = isMagmaMonomorphism
      ; surjective          = surjective
      }

    open IsMagmaIsomorphism isMagmaIsomorphism public
      using (isRelIsomorphism)


------------------------------------------------------------------------
-- Morphisms over group-like structures
------------------------------------------------------------------------

module GroupMorphisms (G₁ : RawGroup a ℓ₁) (G₂ : RawGroup b ℓ₂) where

  open RawGroup G₁ renaming
    (Carrier to A; _≈_ to _≈₁_; _∙_ to _∙_; _⁻¹ to _⁻¹₁; ε to ε₁)
  open RawGroup G₂ renaming
    (Carrier to B; _≈_ to _≈₂_; _∙_ to _◦_; _⁻¹ to _⁻¹₂; ε to ε₂)
  open MorphismDefinitions A B _≈₂_
  open MagmaMorphisms  (RawGroup.rawMagma  G₁) (RawGroup.rawMagma  G₂)
  open MonoidMorphisms (RawGroup.rawMonoid G₁) (RawGroup.rawMonoid G₂)


  record IsGroupHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧
      ⁻¹-homo              : Homomorphic₁ ⟦_⟧ _⁻¹₁ _⁻¹₂

    open IsMonoidHomomorphism isMonoidHomomorphism public


  record IsGroupMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isGroupHomomorphism : IsGroupHomomorphism ⟦_⟧
      injective           : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsGroupHomomorphism isGroupHomomorphism public

    isMonoidMonomorphism : IsMonoidMonomorphism ⟦_⟧
    isMonoidMonomorphism = record
      { isMonoidHomomorphism = isMonoidHomomorphism
      ; injective            = injective
      }

    open IsMonoidMonomorphism isMonoidMonomorphism public
      using (isRelMonomorphism; isMagmaMonomorphism)


  record IsGroupIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isGroupMonomorphism : IsGroupMonomorphism ⟦_⟧
      surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsGroupMonomorphism isGroupMonomorphism public

    isMonoidIsomorphism : IsMonoidIsomorphism ⟦_⟧
    isMonoidIsomorphism = record
      { isMonoidMonomorphism = isMonoidMonomorphism
      ; surjective           = surjective
      }

    open IsMonoidIsomorphism isMonoidIsomorphism public
      using (isRelIsomorphism; isMagmaIsomorphism)


------------------------------------------------------------------------
-- Morphisms over near-semiring-like structures
------------------------------------------------------------------------

module NearSemiringMorphisms (R₁ : RawNearSemiring a ℓ₁) (R₂ : RawNearSemiring b ℓ₂) where

  open RawNearSemiring R₁ renaming
    ( Carrier to A; _≈_ to _≈₁_
    ; +-rawMonoid to +-rawMonoid₁
    ; _*_ to _*₁_
    ; *-rawMagma to *-rawMagma₁)

  open RawNearSemiring R₂ renaming
    ( Carrier to B; _≈_ to _≈₂_
    ; +-rawMonoid to +-rawMonoid₂
    ; _*_ to _*₂_
    ; *-rawMagma to *-rawMagma₂)

  private
    module + = MonoidMorphisms +-rawMonoid₁ +-rawMonoid₂
    module * = MagmaMorphisms *-rawMagma₁ *-rawMagma₂

  open MorphismDefinitions A B _≈₂_


  record IsNearSemiringHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      +-isMonoidHomomorphism : +.IsMonoidHomomorphism ⟦_⟧
      *-homo : Homomorphic₂ ⟦_⟧ _*₁_ _*₂_

    open +.IsMonoidHomomorphism +-isMonoidHomomorphism public
      renaming (homo to +-homo; ε-homo to 0#-homo; isMagmaHomomorphism to +-isMagmaHomomorphism)

    *-isMagmaHomomorphism : *.IsMagmaHomomorphism ⟦_⟧
    *-isMagmaHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; ∙-homo = *-homo
      }

  record IsNearSemiringMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isNearSemiringHomomorphism : IsNearSemiringHomomorphism ⟦_⟧
      injective                  : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsNearSemiringHomomorphism isNearSemiringHomomorphism public

    +-isMonoidMonomorphism : +.IsMonoidMonomorphism ⟦_⟧
    +-isMonoidMonomorphism = record
      { isMonoidHomomorphism = +-isMonoidHomomorphism
      ; injective            = injective
      }

    open +.IsMonoidMonomorphism +-isMonoidMonomorphism public
      using (isRelMonomorphism)
      renaming (isMagmaMonomorphism to +-isMagmaMonomorphsm)

    *-isMagmaMonomorphism : *.IsMagmaMonomorphism ⟦_⟧
    *-isMagmaMonomorphism = record
      { isMagmaHomomorphism = *-isMagmaHomomorphism
      ; injective           = injective
      }

  record IsNearSemiringIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isNearSemiringMonomorphism : IsNearSemiringMonomorphism ⟦_⟧
      surjective                 : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsNearSemiringMonomorphism isNearSemiringMonomorphism public

    +-isMonoidIsomorphism : +.IsMonoidIsomorphism ⟦_⟧
    +-isMonoidIsomorphism = record
      { isMonoidMonomorphism = +-isMonoidMonomorphism
      ; surjective           = surjective
      }

    open +.IsMonoidIsomorphism +-isMonoidIsomorphism public
      using (isRelIsomorphism)
      renaming (isMagmaIsomorphism to +-isMagmaIsomorphism)

    *-isMagmaIsomorphism : *.IsMagmaIsomorphism ⟦_⟧
    *-isMagmaIsomorphism = record
      { isMagmaMonomorphism = *-isMagmaMonomorphism
      ; surjective          = surjective
      }

------------------------------------------------------------------------
-- Morphisms over semiring-like structures
------------------------------------------------------------------------

module SemiringMorphisms (R₁ : RawSemiring a ℓ₁) (R₂ : RawSemiring b ℓ₂) where

  open RawSemiring R₁ renaming
    ( Carrier to A; _≈_ to _≈₁_
    ; 1# to 1#₁
    ; rawNearSemiring to rawNearSemiring₁
    ; *-rawMonoid to *-rawMonoid₁)

  open RawSemiring R₂ renaming
    ( Carrier to B; _≈_ to _≈₂_
    ; 1# to 1#₂
    ; rawNearSemiring to rawNearSemiring₂
    ; *-rawMonoid to *-rawMonoid₂)

  private
    module * = MonoidMorphisms *-rawMonoid₁ *-rawMonoid₂

  open MorphismDefinitions A B _≈₂_
  open NearSemiringMorphisms rawNearSemiring₁ rawNearSemiring₂

  record IsSemiringHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isNearSemiringHomomorphism : IsNearSemiringHomomorphism ⟦_⟧
      1#-homo : Homomorphic₀ ⟦_⟧ 1#₁ 1#₂

    open IsNearSemiringHomomorphism isNearSemiringHomomorphism public

    *-isMonoidHomomorphism : *.IsMonoidHomomorphism ⟦_⟧
    *-isMonoidHomomorphism = record
      { isMagmaHomomorphism = *-isMagmaHomomorphism
      ; ε-homo = 1#-homo
      }

  record IsSemiringMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isSemiringHomomorphism : IsSemiringHomomorphism ⟦_⟧
      injective              : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsSemiringHomomorphism isSemiringHomomorphism public

    isNearSemiringMonomorphism : IsNearSemiringMonomorphism ⟦_⟧
    isNearSemiringMonomorphism = record
      { isNearSemiringHomomorphism = isNearSemiringHomomorphism
      ; injective = injective
      }

    open IsNearSemiringMonomorphism isNearSemiringMonomorphism public
      using (+-isMonoidMonomorphism; *-isMagmaMonomorphism)

    *-isMonoidMonomorphism : *.IsMonoidMonomorphism ⟦_⟧
    *-isMonoidMonomorphism = record
      { isMonoidHomomorphism = *-isMonoidHomomorphism
      ; injective            = injective
      }

  record IsSemiringIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isSemiringMonomorphism : IsSemiringMonomorphism ⟦_⟧
      surjective             : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsSemiringMonomorphism isSemiringMonomorphism public

    isNearSemiringIsomorphism : IsNearSemiringIsomorphism ⟦_⟧
    isNearSemiringIsomorphism = record
      { isNearSemiringMonomorphism = isNearSemiringMonomorphism
      ; surjective = surjective
      }

    open IsNearSemiringIsomorphism isNearSemiringIsomorphism public
      using (+-isMonoidIsomorphism; *-isMagmaIsomorphism)

    *-isMonoidIsomorphism : *.IsMonoidIsomorphism ⟦_⟧
    *-isMonoidIsomorphism = record
      { isMonoidMonomorphism = *-isMonoidMonomorphism
      ; surjective           = surjective
      }

------------------------------------------------------------------------
-- Morphisms over ringWithoutOne-like structures
------------------------------------------------------------------------

module RingWithoutOneMorphisms (R₁ : RawRingWithoutOne a ℓ₁) (R₂ : RawRingWithoutOne b ℓ₂) where

  open RawRingWithoutOne R₁ renaming
    ( Carrier to A; _≈_ to _≈₁_
    ; _*_ to _*₁_
    ; *-rawMagma to *-rawMagma₁
    ; +-rawGroup to +-rawGroup₁
    ; rawNearSemiring to rawNearSemiring₁)

  open RawRingWithoutOne R₂ renaming
    ( Carrier to B; _≈_ to _≈₂_
    ; _*_ to _*₂_
    ; *-rawMagma to *-rawMagma₂
    ; +-rawGroup to +-rawGroup₂
    ; rawNearSemiring to rawNearSemiring₂)

  private
    module + = GroupMorphisms  +-rawGroup₁  +-rawGroup₂
    module * = MagmaMorphisms *-rawMagma₁ *-rawMagma₂
    module +* = NearSemiringMorphisms rawNearSemiring₁ rawNearSemiring₂

  open MorphismDefinitions A B _≈₂_

  record IsRingWithoutOneHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      +-isGroupHomomorphism : +.IsGroupHomomorphism ⟦_⟧
      *-homo : Homomorphic₂ ⟦_⟧ _*₁_ _*₂_

    open +.IsGroupHomomorphism +-isGroupHomomorphism public
      renaming (homo to +-homo; ε-homo to 0#-homo; isMagmaHomomorphism to +-isMagmaHomomorphism; isMonoidHomomorphism to +-isMonoidHomomorphism)

    isNearSemiringHomomorphism : +*.IsNearSemiringHomomorphism ⟦_⟧
    isNearSemiringHomomorphism = record
      { +-isMonoidHomomorphism = +-isMonoidHomomorphism
      ; *-homo = *-homo
      }

    *-isMagmaHomomorphism : *.IsMagmaHomomorphism ⟦_⟧
    *-isMagmaHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; ∙-homo = *-homo
      }

  record IsRingWithoutOneMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRingWithoutOneHomomorphism : IsRingWithoutOneHomomorphism ⟦_⟧
      injective                    : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsRingWithoutOneHomomorphism isRingWithoutOneHomomorphism public

    +-isGroupMonomorphism : +.IsGroupMonomorphism ⟦_⟧
    +-isGroupMonomorphism = record
      { isGroupHomomorphism = +-isGroupHomomorphism
      ; injective           = injective
      }

    open +.IsGroupMonomorphism +-isGroupMonomorphism public
      using (isRelMonomorphism)
      renaming (isMagmaMonomorphism to +-isMagmaMonomorphsm; isMonoidMonomorphism to +-isMonoidMonomorphism)

    *-isMagmaMonomorphism : *.IsMagmaMonomorphism ⟦_⟧
    *-isMagmaMonomorphism = record
      { isMagmaHomomorphism = *-isMagmaHomomorphism
      ; injective           = injective
      }

  record IsRingWithoutOneIsoMorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRingWithoutOneMonomorphism : IsRingWithoutOneMonomorphism ⟦_⟧
      surjective                   : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsRingWithoutOneMonomorphism isRingWithoutOneMonomorphism public

    +-isGroupIsomorphism   : +.IsGroupIsomorphism ⟦_⟧
    +-isGroupIsomorphism  = record
      { isGroupMonomorphism = +-isGroupMonomorphism
      ; surjective          = surjective
      }

    open +.IsGroupIsomorphism +-isGroupIsomorphism public
      using (isRelIsomorphism)
      renaming (isMagmaIsomorphism to +-isMagmaIsomorphism; isMonoidIsomorphism to +-isMonoidIsomorphism)

    *-isMagmaIsomorphism : *.IsMagmaIsomorphism ⟦_⟧
    *-isMagmaIsomorphism = record
      { isMagmaMonomorphism = *-isMagmaMonomorphism
      ; surjective          = surjective
      }


------------------------------------------------------------------------
-- Morphisms over ring-like structures
------------------------------------------------------------------------

module RingMorphisms (R₁ : RawRing a ℓ₁) (R₂ : RawRing b ℓ₂) where

  open RawRing R₁ renaming
    ( Carrier to A; _≈_ to _≈₁_
    ; -_ to -₁_
    ; rawRingWithoutOne to rawRingWithoutOne₁
    ; rawSemiring to rawSemiring₁
    ; *-rawMonoid to *-rawMonoid₁
    ; +-rawGroup to +-rawGroup₁)

  open RawRing R₂ renaming
    ( Carrier to B; _≈_ to _≈₂_
    ; -_ to -₂_
    ; rawRingWithoutOne to rawRingWithoutOne₂
    ; rawSemiring to rawSemiring₂
    ; *-rawMonoid to *-rawMonoid₂
    ; +-rawGroup to +-rawGroup₂)

  module + = GroupMorphisms  +-rawGroup₁  +-rawGroup₂
  module * = MonoidMorphisms *-rawMonoid₁ *-rawMonoid₂
  module *+0 = RingWithoutOneMorphisms rawRingWithoutOne₁ rawRingWithoutOne₂

  open MorphismDefinitions A B _≈₂_
  open SemiringMorphisms rawSemiring₁ rawSemiring₂


  record IsRingHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isSemiringHomomorphism : IsSemiringHomomorphism ⟦_⟧
      -‿homo : Homomorphic₁ ⟦_⟧ -₁_ -₂_

    open IsSemiringHomomorphism isSemiringHomomorphism public

    +-isGroupHomomorphism : +.IsGroupHomomorphism ⟦_⟧
    +-isGroupHomomorphism = record
      { isMonoidHomomorphism = +-isMonoidHomomorphism
      ; ⁻¹-homo = -‿homo
      }

    isRingWithoutOneHomomorphism : *+0.IsRingWithoutOneHomomorphism ⟦_⟧
    isRingWithoutOneHomomorphism = record
      { +-isGroupHomomorphism = +-isGroupHomomorphism
      ; *-homo = *-homo
      }

  record IsRingMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRingHomomorphism : IsRingHomomorphism ⟦_⟧
      injective          : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsRingHomomorphism isRingHomomorphism public

    isSemiringMonomorphism : IsSemiringMonomorphism ⟦_⟧
    isSemiringMonomorphism = record
      { isSemiringHomomorphism = isSemiringHomomorphism
      ; injective = injective
      }

    +-isGroupMonomorphism : +.IsGroupMonomorphism ⟦_⟧
    +-isGroupMonomorphism = record
      { isGroupHomomorphism = +-isGroupHomomorphism
      ; injective           = injective
      }

    open +.IsGroupMonomorphism +-isGroupMonomorphism
      using (isRelMonomorphism)
      renaming ( isMagmaMonomorphism to +-isMagmaMonomorphism
               ; isMonoidMonomorphism to +-isMonoidMonomorphism
               )

    *-isMonoidMonomorphism : *.IsMonoidMonomorphism ⟦_⟧
    *-isMonoidMonomorphism = record
      { isMonoidHomomorphism = *-isMonoidHomomorphism
      ; injective            = injective
      }

    open *.IsMonoidMonomorphism *-isMonoidMonomorphism public
      using ()
      renaming (isMagmaMonomorphism to *-isMagmaMonomorphism)


  record IsRingIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRingMonomorphism : IsRingMonomorphism ⟦_⟧
      surjective         : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsRingMonomorphism isRingMonomorphism public

    isSemiringIsomorphism : IsSemiringIsomorphism ⟦_⟧
    isSemiringIsomorphism = record
      { isSemiringMonomorphism = isSemiringMonomorphism
      ; surjective = surjective
      }

    +-isGroupIsomorphism : +.IsGroupIsomorphism ⟦_⟧
    +-isGroupIsomorphism = record
      { isGroupMonomorphism = +-isGroupMonomorphism
      ; surjective          = surjective
      }

    open +.IsGroupIsomorphism +-isGroupIsomorphism
      using (isRelIsomorphism)
      renaming ( isMagmaIsomorphism to +-isMagmaIsomorphism
               ; isMonoidIsomorphism to +-isMonoidIsomorphisn
               )

    *-isMonoidIsomorphism : *.IsMonoidIsomorphism ⟦_⟧
    *-isMonoidIsomorphism = record
      { isMonoidMonomorphism = *-isMonoidMonomorphism
      ; surjective           = surjective
      }

    open *.IsMonoidIsomorphism *-isMonoidIsomorphism public
      using ()
      renaming (isMagmaIsomorphism to *-isMagmaIsomorphisn)

------------------------------------------------------------------------
-- Morphisms over quasigroup-like structures
------------------------------------------------------------------------

module QuasigroupMorphisms (Q₁ : RawQuasigroup a ℓ₁) (Q₂ : RawQuasigroup b ℓ₂) where

  open RawQuasigroup Q₁ renaming (Carrier to A; ∙-rawMagma to ∙-rawMagma₁;
                                  \\-rawMagma to \\-rawMagma₁; //-rawMagma to //-rawMagma₁;
                                  _≈_ to _≈₁_; _∙_ to _∙₁_; _\\_ to _\\₁_; _//_ to _//₁_)
  open RawQuasigroup Q₂ renaming (Carrier to B; ∙-rawMagma to ∙-rawMagma₂;
                                  \\-rawMagma to \\-rawMagma₂; //-rawMagma to //-rawMagma₂;
                                  _≈_ to _≈₂_; _∙_ to _∙₂_; _\\_ to _\\₂_; _//_ to _//₂_)

  module ∙  = MagmaMorphisms ∙-rawMagma₁ ∙-rawMagma₂
  module \\ = MagmaMorphisms \\-rawMagma₁ \\-rawMagma₂
  module // = MagmaMorphisms //-rawMagma₁ //-rawMagma₂

  open MorphismDefinitions A B _≈₂_

  record IsQuasigroupHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      ∙-homo            : Homomorphic₂ ⟦_⟧ _∙₁_ _∙₂_
      \\-homo           : Homomorphic₂ ⟦_⟧ _\\₁_ _\\₂_
      //-homo           : Homomorphic₂ ⟦_⟧ _//₁_ _//₂_

    open IsRelHomomorphism isRelHomomorphism public
      renaming (cong to ⟦⟧-cong)

    ∙-isMagmaHomomorphism : ∙.IsMagmaHomomorphism ⟦_⟧
    ∙-isMagmaHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; ∙-homo = ∙-homo
      }

    \\-isMagmaHomomorphism : \\.IsMagmaHomomorphism ⟦_⟧
    \\-isMagmaHomomorphism = record
      { isRelHomomorphism  = isRelHomomorphism
      ; ∙-homo = \\-homo
      }

    //-isMagmaHomomorphism : //.IsMagmaHomomorphism ⟦_⟧
    //-isMagmaHomomorphism = record
      { isRelHomomorphism  = isRelHomomorphism
      ; ∙-homo = //-homo
      }

  record IsQuasigroupMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isQuasigroupHomomorphism : IsQuasigroupHomomorphism ⟦_⟧
      injective                : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsQuasigroupHomomorphism isQuasigroupHomomorphism public


    ∙-isMagmaMonomorphism   : ∙.IsMagmaMonomorphism ⟦_⟧
    ∙-isMagmaMonomorphism   = record
      { isMagmaHomomorphism = ∙-isMagmaHomomorphism
      ; injective           = injective
      }

    \\-isMagmaMonomorphism  : \\.IsMagmaMonomorphism ⟦_⟧
    \\-isMagmaMonomorphism  = record
      { isMagmaHomomorphism = \\-isMagmaHomomorphism
      ; injective           = injective
      }

    //-isMagmaMonomorphism  : //.IsMagmaMonomorphism ⟦_⟧
    //-isMagmaMonomorphism  = record
      { isMagmaHomomorphism = //-isMagmaHomomorphism
      ; injective           = injective
      }

    open //.IsMagmaMonomorphism //-isMagmaMonomorphism public
      using (isRelMonomorphism)


  record IsQuasigroupIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isQuasigroupMonomorphism : IsQuasigroupMonomorphism ⟦_⟧
      surjective               : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsQuasigroupMonomorphism isQuasigroupMonomorphism public

    ∙-isMagmaIsomorphism    : ∙.IsMagmaIsomorphism ⟦_⟧
    ∙-isMagmaIsomorphism    = record
      { isMagmaMonomorphism = ∙-isMagmaMonomorphism
      ; surjective          = surjective
      }

    \\-isMagmaIsomorphism   : \\.IsMagmaIsomorphism ⟦_⟧
    \\-isMagmaIsomorphism   = record
      { isMagmaMonomorphism = \\-isMagmaMonomorphism
      ; surjective          = surjective
      }

    //-isMagmaIsomorphism   : //.IsMagmaIsomorphism ⟦_⟧
    //-isMagmaIsomorphism   = record
      { isMagmaMonomorphism = //-isMagmaMonomorphism
      ; surjective          = surjective
      }

    open //.IsMagmaIsomorphism //-isMagmaIsomorphism public
      using (isRelIsomorphism)

------------------------------------------------------------------------
-- Morphisms over loop-like structures
------------------------------------------------------------------------

module LoopMorphisms (L₁ : RawLoop a ℓ₁) (L₂ : RawLoop b ℓ₂) where

  open RawLoop L₁ renaming (Carrier to A; ∙-rawMagma to ∙-rawMagma₁;
                            \\-rawMagma to \\-rawMagma₁; //-rawMagma to //-rawMagma₁;
                             _≈_ to _≈₁_; _∙_ to _∙₁_; _\\_ to _\\₁_; _//_ to _//₁_; ε to ε₁)
  open RawLoop L₂ renaming (Carrier to B; ∙-rawMagma to ∙-rawMagma₂;
                            \\-rawMagma to \\-rawMagma₂; //-rawMagma to //-rawMagma₂;
                            _≈_ to _≈₂_; _∙_ to _∙₂_; _\\_ to _\\₂_; _//_ to _//₂_ ; ε to ε₂)
  open MorphismDefinitions A B _≈₂_

  open QuasigroupMorphisms (RawLoop.rawQuasigroup L₁) (RawLoop.rawQuasigroup L₂)

  record IsLoopHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isQuasigroupHomomorphism : IsQuasigroupHomomorphism ⟦_⟧
      ε-homo                   : Homomorphic₀ ⟦_⟧ ε₁ ε₂

    open IsQuasigroupHomomorphism isQuasigroupHomomorphism public

  record IsLoopMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLoopHomomorphism   : IsLoopHomomorphism ⟦_⟧
      injective            : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsLoopHomomorphism isLoopHomomorphism public

  record IsLoopIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLoopMonomorphism   : IsLoopMonomorphism ⟦_⟧
      surjective           : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsLoopMonomorphism isLoopMonomorphism public

------------------------------------------------------------------------
-- Morphisms over Kleene algebra structures
------------------------------------------------------------------------
module KleeneAlgebraMorphisms (R₁ : RawKleeneAlgebra a ℓ₁) (R₂ : RawKleeneAlgebra b ℓ₂) where

  open RawKleeneAlgebra R₁ renaming
    ( Carrier to A; _≈_ to _≈₁_
    ; _⋆ to _⋆₁
    ; rawSemiring to rawSemiring₁
    )

  open RawKleeneAlgebra R₂ renaming
    ( Carrier to B; _≈_ to _≈₂_
    ; _⋆ to _⋆₂
    ; rawSemiring to rawSemiring₂
    )

  open MorphismDefinitions A B _≈₂_
  open SemiringMorphisms rawSemiring₁ rawSemiring₂

  record IsKleeneAlgebraHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isSemiringHomomorphism : IsSemiringHomomorphism ⟦_⟧
      ⋆-homo :  Homomorphic₁ ⟦_⟧ _⋆₁ _⋆₂

    open IsSemiringHomomorphism isSemiringHomomorphism public

  record IsKleeneAlgebraMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isKleeneAlgebraHomomorphism   : IsKleeneAlgebraHomomorphism ⟦_⟧
      injective                     : Injective  _≈₁_ _≈₂_ ⟦_⟧

    open IsKleeneAlgebraHomomorphism isKleeneAlgebraHomomorphism public

  record IsKleeneAlgebraIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isKleeneAlgebraMonomorphism   : IsKleeneAlgebraMonomorphism ⟦_⟧
      surjective                    : Surjective  _≈₁_ _≈₂_ ⟦_⟧

    open IsKleeneAlgebraMonomorphism isKleeneAlgebraMonomorphism public

------------------------------------------------------------------------
-- Re-export contents of modules publicly

open MagmaMorphisms public
open MonoidMorphisms public
open GroupMorphisms public
open NearSemiringMorphisms public
open SemiringMorphisms public
open RingWithoutOneMorphisms public
open RingMorphisms public
open QuasigroupMorphisms public
open LoopMorphisms public
open KleeneAlgebraMorphisms public
