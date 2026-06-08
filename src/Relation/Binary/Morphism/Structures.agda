------------------------------------------------------------------------
-- The Agda standard library
--
-- Relational morphisms, incl. in particular, order morphisms
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Morphism.Structures
  {a b} {A : Set a} {B : Set b}
  where

open import Data.Product.Base using (_,_)
open import Function.Definitions
  using (Congruent; Injective; Surjective; Bijective)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level


------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

record IsRelHomomorphism (_∼₁_ : Rel A ℓ₁) (_∼₂_ : Rel B ℓ₂)
                         (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    cong : Congruent _∼₁_ _∼₂_ ⟦_⟧


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

  open IsRelMonomorphism isMonomorphism public

  bijective : Bijective _∼₁_ _∼₂_ ⟦_⟧
  bijective = injective , surjective


------------------------------------------------------------------------
-- Orders
------------------------------------------------------------------------

record IsOrderHomomorphism (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
                           (_≲₁_ : Rel A ℓ₃) (_≲₂_ : Rel B ℓ₄)
                           (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                           where
  field
    cong  : Congruent _≈₁_ _≈₂_ ⟦_⟧
    mono  : Congruent _≲₁_ _≲₂_ ⟦_⟧

  module Eq where
    isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelHomomorphism = record { cong = cong }

  isRelHomomorphism : IsRelHomomorphism _≲₁_ _≲₂_ ⟦_⟧
  isRelHomomorphism = record { cong = mono }


record IsOrderMonomorphism (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
                           (_≲₁_ : Rel A ℓ₃) (_≲₂_ : Rel B ℓ₄)
                           (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                           where
  field
    isOrderHomomorphism : IsOrderHomomorphism _≈₁_ _≈₂_ _≲₁_ _≲₂_ ⟦_⟧
    injective           : Injective _≈₁_ _≈₂_ ⟦_⟧
    cancel              : Injective _≲₁_ _≲₂_ ⟦_⟧

  open IsOrderHomomorphism isOrderHomomorphism public
    hiding (module Eq)

  module Eq where
    isRelMonomorphism : IsRelMonomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelMonomorphism = record
      { isHomomorphism = IsOrderHomomorphism.Eq.isRelHomomorphism isOrderHomomorphism
      ; injective      = injective
      }

  isRelMonomorphism : IsRelMonomorphism _≲₁_ _≲₂_ ⟦_⟧
  isRelMonomorphism = record
    { isHomomorphism = isRelHomomorphism
    ; injective      = cancel
    }


record IsOrderIsomorphism (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
                          (_≲₁_ : Rel A ℓ₃) (_≲₂_ : Rel B ℓ₄)
                          (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                          where
  field
    isOrderMonomorphism : IsOrderMonomorphism _≈₁_ _≈₂_ _≲₁_ _≲₂_ ⟦_⟧
    surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

  open IsOrderMonomorphism isOrderMonomorphism public
    hiding (module Eq)

  module Eq where
    isRelIsomorphism : IsRelIsomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelIsomorphism = record
      { isMonomorphism = IsOrderMonomorphism.Eq.isRelMonomorphism isOrderMonomorphism
      ; surjective     = surjective
      }
