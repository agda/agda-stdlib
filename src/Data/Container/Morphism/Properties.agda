------------------------------------------------------------------------
-- The Agda standard library
--
-- Propertiers of any for containers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Morphism.Properties where

open import Level using (_⊔_; suc)
open import Function.Base as F using (_$_)
open import Data.Product.Base using (∃; proj₁; proj₂; _,_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_; _≗_)
open import Data.Container.Core using (Container; _⇒_; ⟦_⟧; position; shape; map; ⟪_⟫)
open import Data.Container.Morphism using (id; _∘_)
open import Data.Container.Relation.Binary.Equality.Setoid using (refl; Eq)
-- Identity

module _ {s p} (C : Container s p) where

  id-correct : ∀ {x} {X : Set x} → ⟪ id C ⟫ {X = X} ≗ F.id
  id-correct x = ≡.refl

-- Composition.

module _ {s₁ s₂ s₃ p₁ p₂ p₃}
         {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂} {C₃ : Container s₃ p₃}
         where

  ∘-correct : (f : C₂ ⇒ C₃) (g : C₁ ⇒ C₂) → ∀ {x} {X : Set x} →
              ⟪ f ∘ g ⟫ {X = X} ≗ (⟪ f ⟫ F.∘ ⟪ g ⟫)
  ∘-correct f g xs = ≡.refl

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂} where

  -- Naturality.

  Natural : ∀ x e → (∀ {X : Set x} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X) →
            Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂ ⊔ suc (x ⊔ e))
  Natural x e m =
    ∀ {X : Set x} (Y : Setoid x e) → let module Y = Setoid Y in
    (f : X → Y.Carrier) (xs : ⟦ C₁ ⟧ X) →
    Eq Y C₂ (m $ map f xs) (map f $ m xs)

  -- Container morphisms are natural.

  natural : ∀ (m : C₁ ⇒ C₂) x e → Natural x e ⟪ m ⟫
  natural m x e Y f xs = refl Y C₂

module _ {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

  -- Natural transformations.

  NT : ∀ x e → Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂ ⊔ suc (x ⊔ e))
  NT x e = ∃ λ (m : ∀ {X : Set x} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X) → Natural x e m

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂} where

  -- All natural functions of the right type are container morphisms.

  complete : ∀ {e} → (nt : NT C₁ C₂ p₁ e) →
      ∃ λ m → (X : Setoid p₁ e) → let module X = Setoid X in
      ∀ xs → Eq X C₂ (proj₁ nt xs) (⟪ m ⟫ xs)
  complete (nt , nat) =
    (m , λ X xs → nat X (proj₂ xs) (proj₁ xs , F.id)) where

    m : C₁ ⇒ C₂
    m .shape    = λ s → proj₁ (nt (s , F.id))
    m .position = proj₂ (nt (_ , F.id))
