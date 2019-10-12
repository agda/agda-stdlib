------------------------------------------------------------------------
-- The Agda standard library
--
-- Morphisms between algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Algebra.Morphism.Structures
  {a ℓ₁} {A : Set a} (_≈₁_ : Rel A ℓ₁) -- Equality over the domain
  {b ℓ₂} {B : Set b} (_≈₂_ : Rel B ℓ₂) -- Equality over the codomain
  where

open import Algebra.Core
open import Algebra.Morphism.Definitions A B _≈₂_
open import Level using (_⊔_)
open import Function.Definitions _≈₁_ _≈₂_
open import Relation.Binary.Morphism.Structures

------------------------------------------------------------------------
-- Morphisms over magma-like structures
------------------------------------------------------------------------

module _ (_∙_ : Op₂ A) (_◦_ : Op₂ B) (⟦_⟧ : A → B) where

  record IsMagmaHomomorphism : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      homo              : Homomorphic₂ ⟦_⟧ _∙_ _◦_

    open IsRelHomomorphism isRelHomomorphism public
      renaming (cong to ⟦⟧-cong)


  record IsMagmaMonomorphism : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMagmaHomomorphism : IsMagmaHomomorphism
      injective           : Injective ⟦_⟧

    open IsMagmaHomomorphism isMagmaHomomorphism public

    isRelMonomorphism : IsRelMonomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelMonomorphism = record
      { isHomomorphism = isRelHomomorphism
      ; injective      = injective
      }


  record IsMagmaIsomorphism : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMagmaMonomorphism : IsMagmaMonomorphism
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

module _ (_∙_ : Op₂ A) (_◦_ : Op₂ B) (ε₁ : A) (ε₂ : B)
         (⟦_⟧ : A → B) where

  record IsMonoidHomomorphism : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMagmaHomomorphism : IsMagmaHomomorphism _∙_ _◦_ ⟦_⟧
      ε-homo              : Homomorphic₀ ⟦_⟧ ε₁ ε₂

    open IsMagmaHomomorphism isMagmaHomomorphism public


  record IsMonoidMonomorphism : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMonoidHomomorphism : IsMonoidHomomorphism
      injective            : Injective ⟦_⟧

    open IsMonoidHomomorphism isMonoidHomomorphism public

    isMagmaMonomorphism : IsMagmaMonomorphism _∙_ _◦_ ⟦_⟧
    isMagmaMonomorphism = record
      { isMagmaHomomorphism = isMagmaHomomorphism
      ; injective           = injective
      }

    open IsMagmaMonomorphism isMagmaMonomorphism public
      using (isRelMonomorphism)


  record IsMonoidIsomorphism : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMonoidMonomorphism : IsMonoidMonomorphism
      surjective           : Surjective ⟦_⟧

    open IsMonoidMonomorphism isMonoidMonomorphism public

    isMagmaIsomorphism : IsMagmaIsomorphism _∙_ _◦_ ⟦_⟧
    isMagmaIsomorphism = record
      { isMagmaMonomorphism = isMagmaMonomorphism
      ; surjective          = surjective
      }

    open IsMagmaIsomorphism isMagmaIsomorphism public
      using (isRelIsomorphism)
