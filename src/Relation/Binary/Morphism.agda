------------------------------------------------------------------------
-- The Agda standard library
--
-- Order morphisms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Morphism where

open import Algebra.Morphism
open import Level
open import Relation.Binary

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

------------------------------------------------------------------------
-- Raw morphisms
------------------------------------------------------------------------

record IsRawRelationMorphism {A : Set a} {B : Set b}
                             (∼₁ : Rel A ℓ₁) (∼₂ : Rel B ℓ₂)
                             (f : A → B)
                             : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    cong : ∼₁ =[ f ]⇒ ∼₂


record IsRawOrderMorphism {A : Set a} {B : Set b}
                          (≈₁ : Rel A ℓ₁) (∼₁ : Rel A ℓ₂)
                          (≈₂ : Rel B ℓ₃) (∼₂ : Rel B ℓ₄)
                          (f : A → B)
                          : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                          where
  field
    cong     : ≈₁ =[ f ]⇒ ≈₂
    monotone : ∼₁ =[ f ]⇒ ∼₂

  module Eq where
    isRawRelationMorphism : IsRawRelationMorphism ≈₁ ≈₂ f
    isRawRelationMorphism = record { cong = cong }

  isRawRelationMorphism : IsRawRelationMorphism ∼₁ ∼₂ f
  isRawRelationMorphism = record { cong = monotone }
