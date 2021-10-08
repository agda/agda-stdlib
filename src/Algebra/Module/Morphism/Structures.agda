------------------------------------------------------------------------
-- The Agda standard library
--
-- Morphisms between module-like algebraic structures
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Morphism.Structures where

open import Algebra.Bundles
open import Algebra.Module.Bundles
import Algebra.Module.Morphism.Definitions as MorphismDefinitions
import Algebra.Morphism.Structures as MorphismStructures
import Function.Definitions as FunctionDefinitions
open import Level

private
  variable
    r ℓr m₁ m₂ ℓm₁ ℓm₂ : Level

module LeftSemimoduleMorphisms
  {semiring : Semiring r ℓr}
  (M₁ : LeftSemimodule semiring m₁ ℓm₁)
  (M₂ : LeftSemimodule semiring m₂ ℓm₂)
  where

  open Semiring semiring renaming (Carrier to R)
  open LeftSemimodule M₁ renaming (Carrierᴹ to A; _*ₗ_ to _*ₗ₁_; _≈ᴹ_ to _≈ᴹ₁_)
  open LeftSemimodule M₂ renaming (Carrierᴹ to B; _*ₗ_ to _*ₗ₂_; _≈ᴹ_ to _≈ᴹ₂_)
  open MorphismDefinitions R A B _≈ᴹ₂_
  open FunctionDefinitions _≈ᴹ₁_ _≈ᴹ₂_
  open MorphismStructures.MonoidMorphisms (LeftSemimodule.+ᴹ-rawMonoid M₁) (LeftSemimodule.+ᴹ-rawMonoid M₂)

  record IsLeftSemimoduleHomomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      +ᴹ-isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧
      *ₗ-homo                 : Homomorphicₗ ⟦_⟧ _*ₗ₁_ _*ₗ₂_

    open IsMonoidHomomorphism +ᴹ-isMonoidHomomorphism public
      using (isRelHomomorphism)
      renaming (isMagmaHomomorphism to +ᴹ-isMagmaHomomorphism; homo to +ᴹ-homo; ε-homo to 0ᴹ-homo)

  record IsLeftSemimoduleMonomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isLeftSemimoduleHomomorphism : IsLeftSemimoduleHomomorphism ⟦_⟧
      injective                    : Injective ⟦_⟧

    open IsLeftSemimoduleHomomorphism isLeftSemimoduleHomomorphism public

    +ᴹ-isMonoidMonomorphism : IsMonoidMonomorphism ⟦_⟧
    +ᴹ-isMonoidMonomorphism = record
      { isMonoidHomomorphism = +ᴹ-isMonoidHomomorphism
      ; injective            = injective
      }

    open IsMonoidMonomorphism +ᴹ-isMonoidMonomorphism public
      using (isRelMonomorphism)
      renaming (isMagmaMonomorphism to +ᴹ-isMagmaMonomorphism)

  record IsLeftSemimoduleIsomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ m₂ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isLeftSemimoduleMonomorphism : IsLeftSemimoduleMonomorphism ⟦_⟧
      surjective                   : Surjective ⟦_⟧

    open IsLeftSemimoduleMonomorphism isLeftSemimoduleMonomorphism public

    +ᴹ-isMonoidIsomorphism : IsMonoidIsomorphism ⟦_⟧
    +ᴹ-isMonoidIsomorphism = record
      { isMonoidMonomorphism = +ᴹ-isMonoidMonomorphism
      ; surjective           = surjective
      }

    open IsMonoidIsomorphism +ᴹ-isMonoidIsomorphism public
      using (isRelIsomorphism)
      renaming (isMagmaIsomorphism to +ᴹ-isMagmaIsomorphism)

module LeftModuleMorphisms
  {ring : Ring r ℓr}
  (M₁ : LeftModule ring m₁ ℓm₁)
  (M₂ : LeftModule ring m₂ ℓm₂)
  where

  open Ring ring renaming (Carrier to R)
  open LeftModule M₁ renaming (Carrierᴹ to A; -ᴹ_ to -ᴹ₁_; _≈ᴹ_ to _≈ᴹ₁_)
  open LeftModule M₂ renaming (Carrierᴹ to B; -ᴹ_ to -ᴹ₂_; _≈ᴹ_ to _≈ᴹ₂_)
  open MorphismDefinitions R A B _≈ᴹ₂_
  open FunctionDefinitions _≈ᴹ₁_ _≈ᴹ₂_
  open MorphismStructures.GroupMorphisms (LeftModule.+ᴹ-rawGroup M₁) (LeftModule.+ᴹ-rawGroup M₂)
  open LeftSemimoduleMorphisms (LeftModule.leftSemimodule M₁) (LeftModule.leftSemimodule M₂)

  record IsLeftModuleHomomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isLeftSemimoduleHomomorphism : IsLeftSemimoduleHomomorphism ⟦_⟧
      -ᴹ-homo                      : Homomorphic₁ ⟦_⟧ -ᴹ₁_ -ᴹ₂_

    open IsLeftSemimoduleHomomorphism isLeftSemimoduleHomomorphism public

    +ᴹ-isGroupHomomorphism : IsGroupHomomorphism ⟦_⟧
    +ᴹ-isGroupHomomorphism = record
      { isMonoidHomomorphism = +ᴹ-isMonoidHomomorphism
      ; ⁻¹-homo              = -ᴹ-homo
      }

  record IsLeftModuleMonomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isLeftModuleHomomorphism : IsLeftModuleHomomorphism ⟦_⟧
      injective                : Injective ⟦_⟧

    open IsLeftModuleHomomorphism isLeftModuleHomomorphism public

    isLeftSemimoduleMonomorphism : IsLeftSemimoduleMonomorphism ⟦_⟧
    isLeftSemimoduleMonomorphism = record
      { isLeftSemimoduleHomomorphism = isLeftSemimoduleHomomorphism
      ; injective                    = injective
      }

    open IsLeftSemimoduleMonomorphism isLeftSemimoduleMonomorphism public
      using (isRelMonomorphism; +ᴹ-isMagmaMonomorphism; +ᴹ-isMonoidMonomorphism)

    +ᴹ-isGroupMonomorphism : IsGroupMonomorphism ⟦_⟧
    +ᴹ-isGroupMonomorphism = record
      { isGroupHomomorphism = +ᴹ-isGroupHomomorphism
      ; injective           = injective
      }

  record IsLeftModuleIsomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ m₂ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isLeftModuleMonomorphism : IsLeftModuleMonomorphism ⟦_⟧
      surjective               : Surjective ⟦_⟧

    open IsLeftModuleMonomorphism isLeftModuleMonomorphism public

    isLeftSemimoduleIsomorphism : IsLeftSemimoduleIsomorphism ⟦_⟧
    isLeftSemimoduleIsomorphism = record
      { isLeftSemimoduleMonomorphism = isLeftSemimoduleMonomorphism
      ; surjective                   = surjective
      }

    open IsLeftSemimoduleIsomorphism isLeftSemimoduleIsomorphism public
      using (isRelIsomorphism; +ᴹ-isMagmaIsomorphism; +ᴹ-isMonoidIsomorphism)

    +ᴹ-isGroupIsomorphism : IsGroupIsomorphism ⟦_⟧
    +ᴹ-isGroupIsomorphism = record
      { isGroupMonomorphism = +ᴹ-isGroupMonomorphism
      ; surjective          = surjective
      }

module RightSemimoduleMorphisms
  {semiring : Semiring r ℓr}
  (M₁ : RightSemimodule semiring m₁ ℓm₁)
  (M₂ : RightSemimodule semiring m₂ ℓm₂)
  where

  open Semiring semiring renaming (Carrier to R)
  open RightSemimodule M₁ renaming (Carrierᴹ to A; _*ᵣ_ to _*ᵣ₁_; _≈ᴹ_ to _≈ᴹ₁_)
  open RightSemimodule M₂ renaming (Carrierᴹ to B; _*ᵣ_ to _*ᵣ₂_; _≈ᴹ_ to _≈ᴹ₂_)
  open MorphismDefinitions R A B _≈ᴹ₂_
  open FunctionDefinitions _≈ᴹ₁_ _≈ᴹ₂_
  open MorphismStructures.MonoidMorphisms (RightSemimodule.+ᴹ-rawMonoid M₁) (RightSemimodule.+ᴹ-rawMonoid M₂)

  record IsRightSemimoduleHomomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      +ᴹ-isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧
      *ᵣ-homo                 : Homomorphicᵣ ⟦_⟧ _*ᵣ₁_ _*ᵣ₂_

    open IsMonoidHomomorphism +ᴹ-isMonoidHomomorphism public
      using (isRelHomomorphism)
      renaming (isMagmaHomomorphism to +ᴹ-isMagmaHomomorphism; homo to +ᴹ-homo; ε-homo to 0ᴹ-homo)

  record IsRightSemimoduleMonomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isRightSemimoduleHomomorphism : IsRightSemimoduleHomomorphism ⟦_⟧
      injective                    : Injective ⟦_⟧

    open IsRightSemimoduleHomomorphism isRightSemimoduleHomomorphism public

    +ᴹ-isMonoidMonomorphism : IsMonoidMonomorphism ⟦_⟧
    +ᴹ-isMonoidMonomorphism = record
      { isMonoidHomomorphism = +ᴹ-isMonoidHomomorphism
      ; injective            = injective
      }

    open IsMonoidMonomorphism +ᴹ-isMonoidMonomorphism public
      using (isRelMonomorphism)
      renaming (isMagmaMonomorphism to +ᴹ-isMagmaMonomorphism)

  record IsRightSemimoduleIsomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ m₂ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isRightSemimoduleMonomorphism : IsRightSemimoduleMonomorphism ⟦_⟧
      surjective                   : Surjective ⟦_⟧

    open IsRightSemimoduleMonomorphism isRightSemimoduleMonomorphism public

    +ᴹ-isMonoidIsomorphism : IsMonoidIsomorphism ⟦_⟧
    +ᴹ-isMonoidIsomorphism = record
      { isMonoidMonomorphism = +ᴹ-isMonoidMonomorphism
      ; surjective           = surjective
      }

    open IsMonoidIsomorphism +ᴹ-isMonoidIsomorphism public
      using (isRelIsomorphism)
      renaming (isMagmaIsomorphism to +ᴹ-isMagmaIsomorphism)

module RightModuleMorphisms
  {ring : Ring r ℓr}
  (M₁ : RightModule ring m₁ ℓm₁)
  (M₂ : RightModule ring m₂ ℓm₂)
  where

  open Ring ring renaming (Carrier to R)
  open RightModule M₁ renaming (Carrierᴹ to A; -ᴹ_ to -ᴹ₁_; _≈ᴹ_ to _≈ᴹ₁_)
  open RightModule M₂ renaming (Carrierᴹ to B; -ᴹ_ to -ᴹ₂_; _≈ᴹ_ to _≈ᴹ₂_)
  open MorphismDefinitions R A B _≈ᴹ₂_
  open FunctionDefinitions _≈ᴹ₁_ _≈ᴹ₂_
  open MorphismStructures.GroupMorphisms (RightModule.+ᴹ-rawGroup M₁) (RightModule.+ᴹ-rawGroup M₂)
  open RightSemimoduleMorphisms (RightModule.rightSemimodule M₁) (RightModule.rightSemimodule M₂)

  record IsRightModuleHomomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isRightSemimoduleHomomorphism : IsRightSemimoduleHomomorphism ⟦_⟧
      -ᴹ-homo                      : Homomorphic₁ ⟦_⟧ -ᴹ₁_ -ᴹ₂_

    open IsRightSemimoduleHomomorphism isRightSemimoduleHomomorphism public

    +ᴹ-isGroupHomomorphism : IsGroupHomomorphism ⟦_⟧
    +ᴹ-isGroupHomomorphism = record
      { isMonoidHomomorphism = +ᴹ-isMonoidHomomorphism
      ; ⁻¹-homo              = -ᴹ-homo
      }

  record IsRightModuleMonomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isRightModuleHomomorphism : IsRightModuleHomomorphism ⟦_⟧
      injective                : Injective ⟦_⟧

    open IsRightModuleHomomorphism isRightModuleHomomorphism public

    isRightSemimoduleMonomorphism : IsRightSemimoduleMonomorphism ⟦_⟧
    isRightSemimoduleMonomorphism = record
      { isRightSemimoduleHomomorphism = isRightSemimoduleHomomorphism
      ; injective                    = injective
      }

    open IsRightSemimoduleMonomorphism isRightSemimoduleMonomorphism public
      using (isRelMonomorphism; +ᴹ-isMagmaMonomorphism; +ᴹ-isMonoidMonomorphism)

    +ᴹ-isGroupMonomorphism : IsGroupMonomorphism ⟦_⟧
    +ᴹ-isGroupMonomorphism = record
      { isGroupHomomorphism = +ᴹ-isGroupHomomorphism
      ; injective           = injective
      }

  record IsRightModuleIsomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ m₂ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isRightModuleMonomorphism : IsRightModuleMonomorphism ⟦_⟧
      surjective               : Surjective ⟦_⟧

    open IsRightModuleMonomorphism isRightModuleMonomorphism public

    isRightSemimoduleIsomorphism : IsRightSemimoduleIsomorphism ⟦_⟧
    isRightSemimoduleIsomorphism = record
      { isRightSemimoduleMonomorphism = isRightSemimoduleMonomorphism
      ; surjective                   = surjective
      }

    open IsRightSemimoduleIsomorphism isRightSemimoduleIsomorphism public
      using (isRelIsomorphism; +ᴹ-isMagmaIsomorphism; +ᴹ-isMonoidIsomorphism)

    +ᴹ-isGroupIsomorphism : IsGroupIsomorphism ⟦_⟧
    +ᴹ-isGroupIsomorphism = record
      { isGroupMonomorphism = +ᴹ-isGroupMonomorphism
      ; surjective          = surjective
      }
