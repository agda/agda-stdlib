------------------------------------------------------------------------
-- The Agda standard library
--
-- Order morphisms bundles
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Morphism.Structures

module Relation.Binary.Morphism.Bundles where

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

module _ (S₁ : Setoid ℓ₁ ℓ₂) (S₂ : Setoid ℓ₃ ℓ₄) where

  record SetoidHomomorphism : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    open Setoid
    field
      ⟦_⟧               : Carrier S₁ → Carrier S₂
      isRelHomomorphism : IsRelHomomorphism (_≈_ S₁) (_≈_ S₂) ⟦_⟧

    open IsRelHomomorphism isRelHomomorphism public


  record SetoidMonomorphism : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    open Setoid
    field
      ⟦_⟧               : Carrier S₁ → Carrier S₂
      isRelMonomorphism : IsRelMonomorphism (_≈_ S₁) (_≈_ S₂) ⟦_⟧

    open IsRelMonomorphism isRelMonomorphism public

    homomorphism : SetoidHomomorphism
    homomorphism = record { isRelHomomorphism = isHomomorphism }


  record SetoidIsomorphism : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    open Setoid
    field
      ⟦_⟧              : Carrier S₁ → Carrier S₂
      isRelIsomorphism : IsRelIsomorphism (_≈_ S₁) (_≈_ S₂) ⟦_⟧

    open IsRelIsomorphism isRelIsomorphism public

    monomorphism : SetoidMonomorphism
    monomorphism = record { isRelMonomorphism = isMonomorphism }

    open SetoidMonomorphism monomorphism public
      using (homomorphism)


------------------------------------------------------------------------
-- Orders
------------------------------------------------------------------------

record PreorderHomomorphism (S₁ : Preorder ℓ₁ ℓ₂ ℓ₃)
                            (S₂ : Preorder ℓ₄ ℓ₅ ℓ₆)
                            : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where
  open Preorder
  field
    ⟦_⟧                 : Carrier S₁ → Carrier S₂
    isOrderHomomorphism : IsOrderHomomorphism (_≈_ S₁) (_≈_ S₂) (_∼_ S₁) (_∼_ S₂) ⟦_⟧

  open IsOrderHomomorphism isOrderHomomorphism public


record PosetHomomorphism (S₁ : Poset ℓ₁ ℓ₂ ℓ₃)
                         (S₂ : Poset ℓ₄ ℓ₅ ℓ₆)
                         : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where
  open Poset
  field
    ⟦_⟧                 : Carrier S₁ → Carrier S₂
    isOrderHomomorphism : IsOrderHomomorphism (_≈_ S₁) (_≈_ S₂) (_≤_ S₁) (_≤_ S₂) ⟦_⟧

  open IsOrderHomomorphism isOrderHomomorphism public
