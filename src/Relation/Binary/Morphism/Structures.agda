------------------------------------------------------------------------
-- The Agda standard library
--
-- Order morphisms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Relation.Binary.Morphism.Structures
  {a b} {A : Set a} {B : Set b}
  where

open import Data.Product using (_,_)
open import Function.Definitions
open import Level
open import Relation.Binary.Morphism.Definitions A B

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

------------------------------------------------------------------------
-- Raw relations
------------------------------------------------------------------------

record IsRelHomomorphism (_∼₁_ : Rel A ℓ₁) (_∼₂_ : Rel B ℓ₂)
                         (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    cong : Homomorphic₂ _∼₁_ _∼₂_ ⟦_⟧


record IsRelMonomorphism (_∼₁_ : Rel A ℓ₁) (_∼₂_ : Rel B ℓ₂)
                         (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isHomomorphism : IsRelHomomorphism _∼₁_ _∼₂_ ⟦_⟧
    injective      : Injective _∼₁_ _∼₂_ ⟦_⟧

  open IsRelHomomorphism isHomomorphism public


record IsRelIsomorphism (_∼₁_ : Rel A ℓ₁) (_∼₂_ : Rel B ℓ₂)
                        (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isMonomorphism : IsRelMonomorphism _∼₁_ _∼₂_ ⟦_⟧
    surjective     : Surjective _∼₁_ _∼₂_ ⟦_⟧

  open IsRelMonomorphism isMonomorphism

  bijective : Bijective _∼₁_ _∼₂_ ⟦_⟧
  bijective = injective , surjective


------------------------------------------------------------------------
-- Raw orders
------------------------------------------------------------------------

record IsOrderHomomorphism (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
                           (_∼₁_ : Rel A ℓ₃) (_∼₂_ : Rel B ℓ₄)
                           (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                           where
  field
    cong  : Homomorphic₂ _≈₁_ _≈₂_ ⟦_⟧
    mono  : Homomorphic₂ _∼₁_ _∼₂_ ⟦_⟧

  module Eq where
    isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelHomomorphism = record { cong = cong }

  isRelHomomorphism : IsRelHomomorphism _∼₁_ _∼₂_ ⟦_⟧
  isRelHomomorphism = record { cong = mono }


record IsOrderMonomorphism (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
                           (_∼₁_ : Rel A ℓ₃) (_∼₂_ : Rel B ℓ₄)
                           (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                           where
  field
    isOrderHomomorphism : IsOrderHomomorphism _≈₁_ _≈₂_ _∼₁_ _∼₂_ ⟦_⟧
    injective           : Injective _≈₁_ _≈₂_ ⟦_⟧
    cancel              : Injective _∼₁_ _∼₂_ ⟦_⟧

  open IsOrderHomomorphism isOrderHomomorphism public
    hiding (module Eq)

  module Eq where
    isRelMonomorphism : IsRelMonomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelMonomorphism = record
      { isHomomorphism = IsOrderHomomorphism.Eq.isRelHomomorphism isOrderHomomorphism
      ; injective      = injective
      }

  isRelMonomorphism : IsRelMonomorphism _∼₁_ _∼₂_ ⟦_⟧
  isRelMonomorphism = record
    { isHomomorphism = isRelHomomorphism
    ; injective      = cancel
    }


record IsOrderIsomorphism (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
                          (_∼₁_ : Rel A ℓ₃) (_∼₂_ : Rel B ℓ₄)
                          (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                          where
  field
    isOrderMonomorphism : IsOrderMonomorphism _≈₁_ _≈₂_ _∼₁_ _∼₂_ ⟦_⟧
    surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

  open IsOrderMonomorphism isOrderMonomorphism public
    hiding (module Eq)

  module Eq where
    isRelIsomorphism : IsRelIsomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelIsomorphism = record
      { isMonomorphism = IsOrderMonomorphism.Eq.isRelMonomorphism isOrderMonomorphism
      ; surjective     = surjective
      }
