------------------------------------------------------------------------
-- The Agda standard library
--
-- Morphisms between algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Algebra.Morphism.Structures where

open import Algebra.Core
open import Algebra.Bundles
import Algebra.Morphism.Definitions as MorphismDefinitions
open import Level using (Level; _⊔_)
import Function.Definitions as FunctionDefinitions
open import Relation.Binary.Morphism.Structures

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Morphisms over magma-like structures
------------------------------------------------------------------------

module MagmaMorphisms (M₁ : RawMagma a ℓ₁) (M₂ : RawMagma b ℓ₂) where

  open RawMagma M₁ renaming (Carrier to A; _≈_ to _≈₁_; _∙_ to _∙_)
  open RawMagma M₂ renaming (Carrier to B; _≈_ to _≈₂_; _∙_ to _◦_)
  open MorphismDefinitions A B _≈₂_
  open FunctionDefinitions _≈₁_ _≈₂_


  record IsMagmaHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      homo              : Homomorphic₂ ⟦_⟧ _∙_ _◦_

    open IsRelHomomorphism isRelHomomorphism public
      renaming (cong to ⟦⟧-cong)


  record IsMagmaMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMagmaHomomorphism : IsMagmaHomomorphism ⟦_⟧
      injective           : Injective ⟦_⟧

    open IsMagmaHomomorphism isMagmaHomomorphism public

    isRelMonomorphism : IsRelMonomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelMonomorphism = record
      { isHomomorphism = isRelHomomorphism
      ; injective      = injective
      }


  record IsMagmaIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMagmaMonomorphism : IsMagmaMonomorphism ⟦_⟧
      surjective          : Surjective ⟦_⟧

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
  open FunctionDefinitions _≈₁_ _≈₂_
  open MagmaMorphisms (RawMonoid.rawMagma M₁) (RawMonoid.rawMagma M₂)

  record IsMonoidHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMagmaHomomorphism : IsMagmaHomomorphism ⟦_⟧
      ε-homo              : Homomorphic₀ ⟦_⟧ ε₁ ε₂

    open IsMagmaHomomorphism isMagmaHomomorphism public

  record IsMonoidMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧
      injective            : Injective ⟦_⟧

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
      surjective           : Surjective ⟦_⟧

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
  open FunctionDefinitions _≈₁_ _≈₂_
  open MagmaMorphisms (RawGroup.rawMagma G₁) (RawGroup.rawMagma G₂)
  open MonoidMorphisms (RawGroup.rawMonoid G₁) (RawGroup.rawMonoid G₂)

  record IsGroupHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧
      ⁻¹-homo              : Homomorphic₁ ⟦_⟧ _⁻¹₁ _⁻¹₂

    open IsMonoidHomomorphism isMonoidHomomorphism public

  record IsGroupMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isGroupHomomorphism : IsGroupHomomorphism ⟦_⟧
      injective           : Injective ⟦_⟧

    open IsGroupHomomorphism isGroupHomomorphism
      renaming (homo to ∙-homo) public

    isMonoidMonomorphism : IsMonoidMonomorphism ⟦_⟧
    isMonoidMonomorphism = record
      { isMonoidHomomorphism = isMonoidHomomorphism
      ; injective            = injective
      }

    open IsMonoidMonomorphism isMonoidMonomorphism public
      using (isRelMonomorphism)

  record IsGroupIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isGroupMonomorphism : IsGroupMonomorphism ⟦_⟧
      surjective          : Surjective ⟦_⟧

    open IsGroupMonomorphism isGroupMonomorphism public

    isMonoidIsomorphism : IsMonoidIsomorphism ⟦_⟧
    isMonoidIsomorphism = record
      { isMonoidMonomorphism = isMonoidMonomorphism
      ; surjective           = surjective
      }

    open IsMonoidIsomorphism isMonoidIsomorphism public
      using (isRelIsomorphism)

------------------------------------------------------------------------
-- Morphisms over ring-like structures
------------------------------------------------------------------------

module RingMorphisms (R₁ : RawRing a ℓ₁) (R₂ : RawRing b ℓ₂) where

  open RawRing R₁ renaming
    ( Carrier to A; _≈_ to _≈₁_
    ; *-rawMonoid to *-rawMonoid₁
    ; +-rawGroup to +-rawGroup₁)

  open RawRing R₂ renaming
    ( Carrier to B; _≈_ to _≈₂_
    ; *-rawMonoid to *-rawMonoid₂
    ; +-rawGroup to +-rawGroup₂)

  module + = GroupMorphisms +-rawGroup₁ +-rawGroup₂
  module * = MonoidMorphisms *-rawMonoid₁ *-rawMonoid₂

  open MorphismDefinitions A B _≈₂_
  open FunctionDefinitions _≈₁_ _≈₂_

  record IsRingHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      +-isGroupHomomorphism  : +.IsGroupHomomorphism  ⟦_⟧
      *-isMonoidHomomorphism : *.IsMonoidHomomorphism ⟦_⟧

    open +.IsGroupHomomorphism +-isGroupHomomorphism renaming
      (homo to +-homo; ε-homo to 0#-homo) public

    open *.IsMonoidHomomorphism *-isMonoidHomomorphism renaming
      (homo to *-homo; ε-homo to 1#-homo) public

  record IsRingMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRingHomomorphism : IsRingHomomorphism ⟦_⟧
      injective          : Injective ⟦_⟧

    open IsRingHomomorphism isRingHomomorphism public

    +-isGroupMonomorphism : +.IsGroupMonomorphism ⟦_⟧
    +-isGroupMonomorphism = record
      { isGroupHomomorphism = +-isGroupHomomorphism
      ; injective           = injective
      }

    *-isMonoidMonomorphism : *.IsMonoidMonomorphism ⟦_⟧
    *-isMonoidMonomorphism = record
      { isMonoidHomomorphism = *-isMonoidHomomorphism
      ; injective            = injective
      }

    open *.IsMonoidMonomorphism *-isMonoidMonomorphism public
      using (isRelMonomorphism)

  record IsRingIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRingMonomorphism : IsRingMonomorphism ⟦_⟧
      surjective         : Surjective ⟦_⟧

    open IsRingMonomorphism isRingMonomorphism public

    +-isGroupIsomorphism : +.IsGroupIsomorphism ⟦_⟧
    +-isGroupIsomorphism = record
      { isGroupMonomorphism = +-isGroupMonomorphism
      ; surjective          = surjective
      }

    *-isMonoidIsomorphism : *.IsMonoidIsomorphism ⟦_⟧
    *-isMonoidIsomorphism = record
      { isMonoidMonomorphism = *-isMonoidMonomorphism
      ; surjective           = surjective
      }

    open *.IsMonoidIsomorphism *-isMonoidIsomorphism public
      using (isRelIsomorphism)

------------------------------------------------------------------------
-- Re-export contents of modules publicly

open MagmaMorphisms public
open MonoidMorphisms public
open GroupMorphisms public
open RingMorphisms public
