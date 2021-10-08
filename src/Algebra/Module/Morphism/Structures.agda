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
