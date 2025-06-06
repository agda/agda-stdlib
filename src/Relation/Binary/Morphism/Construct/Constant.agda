------------------------------------------------------------------------
-- The Agda standard library
--
-- Constant morphisms between binary relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Morphism.Construct.Constant where

open import Function.Base using (const)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid; Preorder)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.Morphism.Structures
  using (IsRelHomomorphism; IsOrderHomomorphism)
open import Relation.Binary.Morphism.Bundles
  using (SetoidHomomorphism; PreorderHomomorphism)

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B : Set a

------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) where

  isRelHomomorphism : Reflexive ≈₂ →
                      ∀ x → IsRelHomomorphism ≈₁ ≈₂ (const x)
  isRelHomomorphism refl x = record
    { cong = const refl
    }

module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) where

  setoidHomomorphism : ∀ x → SetoidHomomorphism S T
  setoidHomomorphism x = record
    { isRelHomomorphism = isRelHomomorphism _ _ T.refl x
    } where module T = Setoid T

------------------------------------------------------------------------
-- Orders
------------------------------------------------------------------------

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) (∼₁ : Rel A ℓ₃) (∼₂ : Rel B ℓ₄) where

  isOrderHomomorphism : Reflexive ≈₂ → Reflexive ∼₂ →
                        ∀ x → IsOrderHomomorphism ≈₁ ≈₂ ∼₁ ∼₂ (const x)
  isOrderHomomorphism ≈-refl ∼-refl x = record
    { cong = const ≈-refl
    ; mono = const ∼-refl
    }

module _ (P : Preorder a ℓ₁ ℓ₂) (Q : Preorder b ℓ₃ ℓ₄) where

  preorderHomomorphism : ∀ x → PreorderHomomorphism P Q
  preorderHomomorphism x = record
    { isOrderHomomorphism = isOrderHomomorphism _ _ _ _ Q.Eq.refl Q.refl x
    } where module Q = Preorder Q
