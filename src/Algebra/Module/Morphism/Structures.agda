------------------------------------------------------------------------
-- The Agda standard library
--
-- Morphisms between module-like algebraic structures
------------------------------------------------------------------------
{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Module.Morphism.Structures where

open import Algebra.Bundles
open import Algebra.Module.Bundles
import Algebra.Module.Morphism.Definitions as MorphismDefinitions
import Algebra.Morphism.Structures as MorphismStructures
import Function.Definitions as FunctionDefinitions
open import Level

private
  variable
    r ℓr s ℓs m₁ m₂ ℓm₁ ℓm₂ : Level

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
      using (isRelHomomorphism; ⟦⟧-cong)
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
  open LeftModule M₁ renaming (Carrierᴹ to A; _*ₗ_ to _*ₗ₁_; _≈ᴹ_ to _≈ᴹ₁_)
  open LeftModule M₂ renaming (Carrierᴹ to B; _*ₗ_ to _*ₗ₂_; _≈ᴹ_ to _≈ᴹ₂_)
  open MorphismDefinitions R A B _≈ᴹ₂_
  open FunctionDefinitions _≈ᴹ₁_ _≈ᴹ₂_
  open MorphismStructures.GroupMorphisms (LeftModule.+ᴹ-rawGroup M₁) (LeftModule.+ᴹ-rawGroup M₂)
  open LeftSemimoduleMorphisms (LeftModule.leftSemimodule M₁) (LeftModule.leftSemimodule M₂)

  record IsLeftModuleHomomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      +ᴹ-isGroupHomomorphism : IsGroupHomomorphism ⟦_⟧
      *ₗ-homo                : Homomorphicₗ ⟦_⟧ _*ₗ₁_ _*ₗ₂_

    open IsGroupHomomorphism +ᴹ-isGroupHomomorphism public
      using (isRelHomomorphism; ⟦⟧-cong)
      renaming ( isMagmaHomomorphism to +ᴹ-isMagmaHomomorphism; isMonoidHomomorphism to +ᴹ-isMonoidHomomorphism
               ; homo to +ᴹ-homo; ε-homo to 0ᴹ-homo; ⁻¹-homo to -ᴹ-homo
               )

    isLeftSemimoduleHomomorphism : IsLeftSemimoduleHomomorphism ⟦_⟧
    isLeftSemimoduleHomomorphism = record
      { +ᴹ-isMonoidHomomorphism = +ᴹ-isMonoidHomomorphism
      ; *ₗ-homo                 = *ₗ-homo
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
      using (isRelHomomorphism; ⟦⟧-cong)
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
  open RightModule M₁ renaming (Carrierᴹ to A; _*ᵣ_ to _*ᵣ₁_; _≈ᴹ_ to _≈ᴹ₁_)
  open RightModule M₂ renaming (Carrierᴹ to B; _*ᵣ_ to _*ᵣ₂_; _≈ᴹ_ to _≈ᴹ₂_)
  open MorphismDefinitions R A B _≈ᴹ₂_
  open FunctionDefinitions _≈ᴹ₁_ _≈ᴹ₂_
  open MorphismStructures.GroupMorphisms (RightModule.+ᴹ-rawGroup M₁) (RightModule.+ᴹ-rawGroup M₂)
  open RightSemimoduleMorphisms (RightModule.rightSemimodule M₁) (RightModule.rightSemimodule M₂)

  record IsRightModuleHomomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      +ᴹ-isGroupHomomorphism : IsGroupHomomorphism ⟦_⟧
      *ᵣ-homo                : Homomorphicᵣ ⟦_⟧ _*ᵣ₁_ _*ᵣ₂_

    open IsGroupHomomorphism +ᴹ-isGroupHomomorphism public
      using (isRelHomomorphism; ⟦⟧-cong)
      renaming ( isMagmaHomomorphism to +ᴹ-isMagmaHomomorphism; isMonoidHomomorphism to +ᴹ-isMonoidHomomorphism
               ; homo to +ᴹ-homo; ε-homo to 0ᴹ-homo; ⁻¹-homo to -ᴹ-homo
               )
    isRightSemimoduleHomomorphism : IsRightSemimoduleHomomorphism ⟦_⟧
    isRightSemimoduleHomomorphism = record
      { +ᴹ-isMonoidHomomorphism = +ᴹ-isMonoidHomomorphism
      ; *ᵣ-homo                 = *ᵣ-homo
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

module BisemimoduleMorphisms
  {R-semiring : Semiring r ℓr}
  {S-semiring : Semiring s ℓs}
  (M₁ : Bisemimodule R-semiring S-semiring m₁ ℓm₁)
  (M₂ : Bisemimodule R-semiring S-semiring m₂ ℓm₂)
  where

  open Semiring R-semiring renaming (Carrier to R)
  open Semiring S-semiring renaming (Carrier to S)
  open Bisemimodule M₁ renaming (Carrierᴹ to A; _*ₗ_ to _*ₗ₁_; _*ᵣ_ to _*ᵣ₁_; _≈ᴹ_ to _≈ᴹ₁_)
  open Bisemimodule M₂ renaming (Carrierᴹ to B; _*ₗ_ to _*ₗ₂_; _*ᵣ_ to _*ᵣ₂_; _≈ᴹ_ to _≈ᴹ₂_)
  open MorphismDefinitions R A B _≈ᴹ₂_ using (Homomorphicₗ)
  open MorphismDefinitions S A B _≈ᴹ₂_ using (Homomorphicᵣ)
  open FunctionDefinitions _≈ᴹ₁_ _≈ᴹ₂_
  open MorphismStructures.MonoidMorphisms (Bisemimodule.+ᴹ-rawMonoid M₁) (Bisemimodule.+ᴹ-rawMonoid M₂)
  open LeftSemimoduleMorphisms (Bisemimodule.leftSemimodule M₁) (Bisemimodule.leftSemimodule M₂)
  open RightSemimoduleMorphisms (Bisemimodule.rightSemimodule M₁) (Bisemimodule.rightSemimodule M₂)

  record IsBisemimoduleHomomorphism (⟦_⟧ : A → B) : Set (r ⊔ s ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      +ᴹ-isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧
      *ₗ-homo                 : Homomorphicₗ ⟦_⟧ _*ₗ₁_ _*ₗ₂_
      *ᵣ-homo                 : Homomorphicᵣ ⟦_⟧ _*ᵣ₁_ _*ᵣ₂_

    isLeftSemimoduleHomomorphism : IsLeftSemimoduleHomomorphism ⟦_⟧
    isLeftSemimoduleHomomorphism = record
      { +ᴹ-isMonoidHomomorphism = +ᴹ-isMonoidHomomorphism
      ; *ₗ-homo                 = *ₗ-homo
      }

    open IsLeftSemimoduleHomomorphism isLeftSemimoduleHomomorphism public
      using (isRelHomomorphism; ⟦⟧-cong; +ᴹ-isMagmaHomomorphism; +ᴹ-homo; 0ᴹ-homo)

    isRightSemimoduleHomomorphism : IsRightSemimoduleHomomorphism ⟦_⟧
    isRightSemimoduleHomomorphism = record
      { +ᴹ-isMonoidHomomorphism = +ᴹ-isMonoidHomomorphism
      ; *ᵣ-homo                 = *ᵣ-homo
      }

  record IsBisemimoduleMonomorphism (⟦_⟧ : A → B) : Set (r ⊔ s ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isBisemimoduleHomomorphism : IsBisemimoduleHomomorphism ⟦_⟧
      injective                  : Injective ⟦_⟧

    open IsBisemimoduleHomomorphism isBisemimoduleHomomorphism public

    isLeftSemimoduleMonomorphism : IsLeftSemimoduleMonomorphism ⟦_⟧
    isLeftSemimoduleMonomorphism = record
      { isLeftSemimoduleHomomorphism = isLeftSemimoduleHomomorphism
      ; injective                    = injective
      }

    open IsLeftSemimoduleMonomorphism isLeftSemimoduleMonomorphism public
      using (isRelMonomorphism; +ᴹ-isMagmaMonomorphism; +ᴹ-isMonoidMonomorphism)

    isRightSemimoduleMonomorphism : IsRightSemimoduleMonomorphism ⟦_⟧
    isRightSemimoduleMonomorphism = record
      { isRightSemimoduleHomomorphism = isRightSemimoduleHomomorphism
      ; injective                     = injective
      }

  record IsBisemimoduleIsomorphism (⟦_⟧ : A → B) : Set (r ⊔ s ⊔ m₁ ⊔ m₂ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isBisemimoduleMonomorphism : IsBisemimoduleMonomorphism ⟦_⟧
      surjective                 : Surjective ⟦_⟧

    open IsBisemimoduleMonomorphism isBisemimoduleMonomorphism public

    isLeftSemimoduleIsomorphism : IsLeftSemimoduleIsomorphism ⟦_⟧
    isLeftSemimoduleIsomorphism = record
      { isLeftSemimoduleMonomorphism = isLeftSemimoduleMonomorphism
      ; surjective                   = surjective
      }

    open IsLeftSemimoduleIsomorphism isLeftSemimoduleIsomorphism public
      using (isRelIsomorphism; +ᴹ-isMagmaIsomorphism; +ᴹ-isMonoidIsomorphism)

    isRightSemimoduleIsomorphism : IsRightSemimoduleIsomorphism ⟦_⟧
    isRightSemimoduleIsomorphism = record
      { isRightSemimoduleMonomorphism = isRightSemimoduleMonomorphism
      ; surjective                    = surjective
      }

module BimoduleMorphisms
  {R-ring : Ring r ℓr}
  {S-ring : Ring s ℓs}
  (M₁ : Bimodule R-ring S-ring m₁ ℓm₁)
  (M₂ : Bimodule R-ring S-ring m₂ ℓm₂)
  where

  open Ring R-ring renaming (Carrier to R)
  open Ring S-ring renaming (Carrier to S)
  open Bimodule M₁ renaming (Carrierᴹ to A; _*ₗ_ to _*ₗ₁_; _*ᵣ_ to _*ᵣ₁_; _≈ᴹ_ to _≈ᴹ₁_)
  open Bimodule M₂ renaming (Carrierᴹ to B; _*ₗ_ to _*ₗ₂_; _*ᵣ_ to _*ᵣ₂_; _≈ᴹ_ to _≈ᴹ₂_)
  open MorphismDefinitions R A B _≈ᴹ₂_ using (Homomorphicₗ)
  open MorphismDefinitions S A B _≈ᴹ₂_ using (Homomorphicᵣ)
  open FunctionDefinitions _≈ᴹ₁_ _≈ᴹ₂_
  open MorphismStructures.GroupMorphisms (Bimodule.+ᴹ-rawGroup M₁) (Bimodule.+ᴹ-rawGroup M₂)
  open LeftModuleMorphisms (Bimodule.leftModule M₁) (Bimodule.leftModule M₂)
  open RightModuleMorphisms (Bimodule.rightModule M₁) (Bimodule.rightModule M₂)
  open BisemimoduleMorphisms (Bimodule.bisemimodule M₁) (Bimodule.bisemimodule M₂)

  record IsBimoduleHomomorphism (⟦_⟧ : A → B) : Set (r ⊔ s ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      +ᴹ-isGroupHomomorphism : IsGroupHomomorphism ⟦_⟧
      *ₗ-homo                 : Homomorphicₗ ⟦_⟧ _*ₗ₁_ _*ₗ₂_
      *ᵣ-homo                 : Homomorphicᵣ ⟦_⟧ _*ᵣ₁_ _*ᵣ₂_

    open IsGroupHomomorphism +ᴹ-isGroupHomomorphism public
      using (isRelHomomorphism; ⟦⟧-cong)
      renaming ( isMagmaHomomorphism to +ᴹ-isMagmaHomomorphism; isMonoidHomomorphism to +ᴹ-isMonoidHomomorphism
               ; homo to +ᴹ-homo; ε-homo to 0ᴹ-homo; ⁻¹-homo to -ᴹ-homo
               )

    isBisemimoduleHomomorphism : IsBisemimoduleHomomorphism ⟦_⟧
    isBisemimoduleHomomorphism = record
      { +ᴹ-isMonoidHomomorphism = +ᴹ-isMonoidHomomorphism
      ; *ₗ-homo                 = *ₗ-homo
      ; *ᵣ-homo                 = *ᵣ-homo
      }

    open IsBisemimoduleHomomorphism isBisemimoduleHomomorphism public
      using (isLeftSemimoduleHomomorphism; isRightSemimoduleHomomorphism)

    isLeftModuleHomomorphism : IsLeftModuleHomomorphism ⟦_⟧
    isLeftModuleHomomorphism = record
      { +ᴹ-isGroupHomomorphism = +ᴹ-isGroupHomomorphism
      ; *ₗ-homo                = *ₗ-homo
      }

    isRightModuleHomomorphism : IsRightModuleHomomorphism ⟦_⟧
    isRightModuleHomomorphism = record
      { +ᴹ-isGroupHomomorphism = +ᴹ-isGroupHomomorphism
      ; *ᵣ-homo                = *ᵣ-homo
      }

  record IsBimoduleMonomorphism (⟦_⟧ : A → B) : Set (r ⊔ s ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isBimoduleHomomorphism : IsBimoduleHomomorphism ⟦_⟧
      injective              : Injective ⟦_⟧

    open IsBimoduleHomomorphism isBimoduleHomomorphism public

    +ᴹ-isGroupMonomorphism : IsGroupMonomorphism ⟦_⟧
    +ᴹ-isGroupMonomorphism = record
      { isGroupHomomorphism = +ᴹ-isGroupHomomorphism
      ; injective           = injective
      }

    open IsGroupMonomorphism +ᴹ-isGroupMonomorphism public
      using (isRelMonomorphism)
      renaming (isMagmaMonomorphism to +ᴹ-isMagmaMonomorphism; isMonoidMonomorphism to +ᴹ-isMonoidMonomorphism)

    isLeftModuleMonomorphism : IsLeftModuleMonomorphism ⟦_⟧
    isLeftModuleMonomorphism = record
      { isLeftModuleHomomorphism = isLeftModuleHomomorphism
      ; injective                = injective
      }

    open IsLeftModuleMonomorphism isLeftModuleMonomorphism public
      using (isLeftSemimoduleMonomorphism)

    isRightModuleMonomorphism : IsRightModuleMonomorphism ⟦_⟧
    isRightModuleMonomorphism = record
      { isRightModuleHomomorphism = isRightModuleHomomorphism
      ; injective                 = injective
      }

    open IsRightModuleMonomorphism isRightModuleMonomorphism public
      using (isRightSemimoduleMonomorphism)

    isBisemimoduleMonomorphism : IsBisemimoduleMonomorphism ⟦_⟧
    isBisemimoduleMonomorphism = record
      { isBisemimoduleHomomorphism = isBisemimoduleHomomorphism
      ; injective                  = injective
      }

  record IsBimoduleIsomorphism (⟦_⟧ : A → B) : Set (r ⊔ s ⊔ m₁ ⊔ m₂ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isBimoduleMonomorphism : IsBimoduleMonomorphism ⟦_⟧
      surjective             : Surjective ⟦_⟧

    open IsBimoduleMonomorphism isBimoduleMonomorphism public

    +ᴹ-isGroupIsomorphism : IsGroupIsomorphism ⟦_⟧
    +ᴹ-isGroupIsomorphism = record
      { isGroupMonomorphism = +ᴹ-isGroupMonomorphism
      ; surjective          = surjective
      }

    open IsGroupIsomorphism +ᴹ-isGroupIsomorphism public
      using (isRelIsomorphism)
      renaming (isMagmaIsomorphism to +ᴹ-isMagmaIsomorphism; isMonoidIsomorphism to +ᴹ-isMonoidIsomorphism)

    isLeftModuleIsomorphism : IsLeftModuleIsomorphism ⟦_⟧
    isLeftModuleIsomorphism = record
      { isLeftModuleMonomorphism = isLeftModuleMonomorphism
      ; surjective               = surjective
      }

    open IsLeftModuleIsomorphism isLeftModuleIsomorphism public
      using (isLeftSemimoduleIsomorphism)

    isRightModuleIsomorphism : IsRightModuleIsomorphism ⟦_⟧
    isRightModuleIsomorphism = record
      { isRightModuleMonomorphism = isRightModuleMonomorphism
      ; surjective                = surjective
      }

    open IsRightModuleIsomorphism isRightModuleIsomorphism public
      using (isRightSemimoduleIsomorphism)

    isBisemimoduleIsomorphism : IsBisemimoduleIsomorphism ⟦_⟧
    isBisemimoduleIsomorphism = record
      { isBisemimoduleMonomorphism = isBisemimoduleMonomorphism
      ; surjective                 = surjective
      }

module SemimoduleMorphisms
  {commutativeSemiring : CommutativeSemiring r ℓr}
  (M₁ : Semimodule commutativeSemiring m₁ ℓm₁)
  (M₂ : Semimodule commutativeSemiring m₂ ℓm₂)
  where

  open Semimodule M₁ renaming (Carrierᴹ to A; _≈ᴹ_ to _≈ᴹ₁_)
  open Semimodule M₂ renaming (Carrierᴹ to B; _≈ᴹ_ to _≈ᴹ₂_)
  open FunctionDefinitions _≈ᴹ₁_ _≈ᴹ₂_
  open BisemimoduleMorphisms (Semimodule.bisemimodule M₁) (Semimodule.bisemimodule M₂)

  record IsSemimoduleHomomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isBisemimoduleHomomorphism : IsBisemimoduleHomomorphism ⟦_⟧

    open IsBisemimoduleHomomorphism isBisemimoduleHomomorphism public

  record IsSemimoduleMonomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isSemimoduleHomomorphism : IsSemimoduleHomomorphism ⟦_⟧
      injective                : Injective ⟦_⟧

    open IsSemimoduleHomomorphism isSemimoduleHomomorphism public

    isBisemimoduleMonomorphism : IsBisemimoduleMonomorphism ⟦_⟧
    isBisemimoduleMonomorphism = record
      { isBisemimoduleHomomorphism = isBisemimoduleHomomorphism
      ; injective                  = injective
      }

    open IsBisemimoduleMonomorphism isBisemimoduleMonomorphism public
      using ( isRelMonomorphism; +ᴹ-isMagmaMonomorphism; +ᴹ-isMonoidMonomorphism
            ; isLeftSemimoduleMonomorphism; isRightSemimoduleMonomorphism
            )

  record IsSemimoduleIsomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ m₂ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isSemimoduleMonomorphism : IsSemimoduleMonomorphism ⟦_⟧
      surjective               : Surjective ⟦_⟧

    open IsSemimoduleMonomorphism isSemimoduleMonomorphism public

    isBisemimoduleIsomorphism : IsBisemimoduleIsomorphism ⟦_⟧
    isBisemimoduleIsomorphism = record
      { isBisemimoduleMonomorphism = isBisemimoduleMonomorphism
      ; surjective                 = surjective
      }

    open IsBisemimoduleIsomorphism isBisemimoduleIsomorphism public
      using ( isRelIsomorphism; +ᴹ-isMagmaIsomorphism; +ᴹ-isMonoidIsomorphism
            ; isLeftSemimoduleIsomorphism; isRightSemimoduleIsomorphism
            )

module ModuleMorphisms
  {commutativeRing : CommutativeRing r ℓr}
  (M₁ : Module commutativeRing m₁ ℓm₁)
  (M₂ : Module commutativeRing m₂ ℓm₂)
  where

  open Module M₁ renaming (Carrierᴹ to A; _≈ᴹ_ to _≈ᴹ₁_)
  open Module M₂ renaming (Carrierᴹ to B; _≈ᴹ_ to _≈ᴹ₂_)
  open FunctionDefinitions _≈ᴹ₁_ _≈ᴹ₂_
  open BimoduleMorphisms (Module.bimodule M₁) (Module.bimodule M₂)
  open SemimoduleMorphisms (Module.semimodule M₁) (Module.semimodule M₂)

  record IsModuleHomomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isBimoduleHomomorphism : IsBimoduleHomomorphism ⟦_⟧

    open IsBimoduleHomomorphism isBimoduleHomomorphism public

    isSemimoduleHomomorphism : IsSemimoduleHomomorphism ⟦_⟧
    isSemimoduleHomomorphism = record
      { isBisemimoduleHomomorphism = isBisemimoduleHomomorphism
      }

  record IsModuleMonomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isModuleHomomorphism : IsModuleHomomorphism ⟦_⟧
      injective            : Injective ⟦_⟧

    open IsModuleHomomorphism isModuleHomomorphism public

    isBimoduleMonomorphism : IsBimoduleMonomorphism ⟦_⟧
    isBimoduleMonomorphism = record
      { isBimoduleHomomorphism = isBimoduleHomomorphism
      ; injective              = injective
      }

    open IsBimoduleMonomorphism isBimoduleMonomorphism public
      using ( isRelMonomorphism; +ᴹ-isMagmaMonomorphism; +ᴹ-isMonoidMonomorphism; +ᴹ-isGroupMonomorphism
            ; isLeftSemimoduleMonomorphism; isRightSemimoduleMonomorphism; isBisemimoduleMonomorphism
            ; isLeftModuleMonomorphism; isRightModuleMonomorphism
            )

    isSemimoduleMonomorphism : IsSemimoduleMonomorphism ⟦_⟧
    isSemimoduleMonomorphism = record
      { isSemimoduleHomomorphism = isSemimoduleHomomorphism
      ; injective                = injective
      }

  record IsModuleIsomorphism (⟦_⟧ : A → B) : Set (r ⊔ m₁ ⊔ m₂ ⊔ ℓm₁ ⊔ ℓm₂) where
    field
      isModuleMonomorphism : IsModuleMonomorphism ⟦_⟧
      surjective           : Surjective ⟦_⟧

    open IsModuleMonomorphism isModuleMonomorphism public

    isBimoduleIsomorphism : IsBimoduleIsomorphism ⟦_⟧
    isBimoduleIsomorphism = record
      { isBimoduleMonomorphism = isBimoduleMonomorphism
      ; surjective             = surjective
      }

    open IsBimoduleIsomorphism isBimoduleIsomorphism public
      using ( isRelIsomorphism; +ᴹ-isMagmaIsomorphism; +ᴹ-isMonoidIsomorphism; +ᴹ-isGroupIsomorphism
            ; isLeftSemimoduleIsomorphism; isRightSemimoduleIsomorphism; isBisemimoduleIsomorphism
            ; isLeftModuleIsomorphism; isRightModuleIsomorphism
            )

    isSemimoduleIsomorphism : IsSemimoduleIsomorphism ⟦_⟧
    isSemimoduleIsomorphism = record
      { isSemimoduleMonomorphism = isSemimoduleMonomorphism
      ; surjective               = surjective
      }

open LeftSemimoduleMorphisms public
open LeftModuleMorphisms public
open RightSemimoduleMorphisms public
open RightModuleMorphisms public
open BisemimoduleMorphisms public
open BimoduleMorphisms public
open SemimoduleMorphisms public
open ModuleMorphisms public
