------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for morphisms between binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.Bundles
open import Relation.Binary.Morphism.Structures
open import Relation.Binary.Consequences using (mono⇒cong)

module Relation.Binary.Morphism.Bundles where

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

------------------------------------------------------------------------
-- Setoids
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
-- Preorders
------------------------------------------------------------------------

record PreorderHomomorphism (S₁ : Preorder ℓ₁ ℓ₂ ℓ₃)
                            (S₂ : Preorder ℓ₄ ℓ₅ ℓ₆)
                            : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where
  open Preorder
  field
    ⟦_⟧                 : Carrier S₁ → Carrier S₂
    isOrderHomomorphism : IsOrderHomomorphism (_≈_ S₁) (_≈_ S₂) (_∼_ S₁) (_∼_ S₂) ⟦_⟧

  open IsOrderHomomorphism isOrderHomomorphism public

------------------------------------------------------------------------
-- Posets
------------------------------------------------------------------------

module _ (P : Poset ℓ₁ ℓ₂ ℓ₃) (Q : Poset ℓ₄ ℓ₅ ℓ₆) where

  private
    module P = Poset P
    module Q = Poset Q

  record PosetHomomorphism : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where
    field
      ⟦_⟧                 : P.Carrier → Q.Carrier
      isOrderHomomorphism : IsOrderHomomorphism P._≈_ Q._≈_ P._≤_ Q._≤_ ⟦_⟧

    open IsOrderHomomorphism isOrderHomomorphism public


  -- Smart constructor that automatically constructs the congruence proof
  -- from the monotonicity proof
  mkPosetHomo : ∀ f → f Preserves P._≤_ ⟶ Q._≤_ → PosetHomomorphism
  mkPosetHomo f mono = record
    { ⟦_⟧ = f
    ; isOrderHomomorphism = record
      { cong = mono⇒cong P._≈_ Q._≈_ P.Eq.sym P.reflexive Q.antisym mono
      ; mono = mono
      }
    }
