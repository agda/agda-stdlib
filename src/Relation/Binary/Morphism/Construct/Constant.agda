------------------------------------------------------------------------
-- The Agda standard library
--
-- Constant morphisms between binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Product using (_,_)
open import Function.Base using (const; _∘_)
open import Function.Definitions using (Congruent)
open import Function.Construct.Composition using (surjective)
open import Relation.Binary
open import Relation.Binary.Morphism.Structures

module Relation.Binary.Morphism.Construct.Constant
  {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
  (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) (≈-refl : Reflexive ≈₂)
  where

------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

isRelHomomorphism : ∀ x → IsRelHomomorphism ≈₁ ≈₂ (const x)
isRelHomomorphism x = record
  { cong = const ≈-refl
  }

------------------------------------------------------------------------
-- Orders
------------------------------------------------------------------------

module _ {ℓ₃ ℓ₄} (∼₁ : Rel A ℓ₃) (∼₂ : Rel B ℓ₄) where

  isOrderHomomorphism : Reflexive ∼₂ →
                        ∀ x → IsOrderHomomorphism ≈₁ ≈₂ ∼₁ ∼₂ (const x)
  isOrderHomomorphism ∼-refl x = record
    { cong = const ≈-refl
    ; mono = const ∼-refl
    }
