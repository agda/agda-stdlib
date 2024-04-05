------------------------------------------------------------------------
-- The Agda standard library
--
-- Correctness proofs for container combinators
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Container.Combinator.Properties where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Container.Core using (Container; ⟦_⟧)
open import Data.Container.Combinator
open import Data.Empty using (⊥-elim)
open import Data.Product.Base as P using (∃; _,_; proj₁; proj₂; <_,_>; uncurry; curry)
open import Data.Sum.Base as S using (inj₁; inj₂; [_,_]′; [_,_])
open import Function.Base as F using (_∘′_)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Level using (_⊔_; lower)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≗_; refl; cong)

-- I have proved some of the correctness statements under the
-- assumption of functional extensionality. I could have reformulated
-- the statements using suitable setoids, but I could not be bothered.

module Identity where

  correct : ∀ {s p x} {X : Set x} → ⟦ id {s} {p} ⟧ X ↔ F.id X
  correct {X = X} = mk↔ₛ′ from-id to-id (λ _ → refl) (λ _ → refl)

module Constant (ext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

  correct : ∀ {x p y} (X : Set x) {Y : Set y} → ⟦ const {x} {p ⊔ y} X ⟧ Y ↔ F.const X Y
  correct {x} {y} X {Y} = mk↔ₛ′ (from-const X) (to-const X) (λ _ → refl) from∘to
    where
    from∘to : (x : ⟦ const X ⟧ Y) → to-const X (proj₁ x) ≡ x
    from∘to xs = cong (proj₁ xs ,_) (ext (λ x → ⊥-elim (lower x)))

module Composition {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

  correct : ∀ {x} {X : Set x} → ⟦ C₁ ∘ C₂ ⟧ X ↔ (⟦ C₁ ⟧ F.∘ ⟦ C₂ ⟧) X
  correct {X = X} = mk↔ₛ′ (from-∘ C₁ C₂) (to-∘ C₁ C₂) (λ _ → refl) (λ _ → refl)

module Product (ext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′)
       {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

  correct : ∀ {x} {X : Set x} →  ⟦ C₁ × C₂ ⟧ X ↔ (⟦ C₁ ⟧ X P.× ⟦ C₂ ⟧ X)
  correct {X = X} = mk↔ₛ′ (from-× C₁ C₂) (to-× C₁ C₂) (λ _ → refl) from∘to
    where
    from∘to : (to-× C₁ C₂) F.∘ (from-× C₁ C₂) ≗ F.id
    from∘to (s , f) =
      cong (s ,_) (ext [ (λ _ → refl) , (λ _ → refl) ])

module IndexedProduct {i s p} {I : Set i} (Cᵢ : I → Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ Π I Cᵢ ⟧ X ↔ (∀ i → ⟦ Cᵢ i ⟧ X)
  correct {X = X} = mk↔ₛ′ (from-Π I Cᵢ) (to-Π I Cᵢ) (λ _ → refl) (λ _ → refl)

module Sum {s₁ s₂ p} (C₁ : Container s₁ p) (C₂ : Container s₂ p) where

  correct : ∀ {x} {X : Set x} → ⟦ C₁ ⊎ C₂ ⟧ X ↔ (⟦ C₁ ⟧ X S.⊎ ⟦ C₂ ⟧ X)
  correct {X = X} = mk↔ₛ′ (from-⊎ C₁ C₂) (to-⊎ C₁ C₂) to∘from from∘to
    where
    from∘to : (to-⊎ C₁ C₂) F.∘ (from-⊎ C₁ C₂) ≗ F.id
    from∘to (inj₁ s₁ , f) = refl
    from∘to (inj₂ s₂ , f) = refl

    to∘from : (from-⊎ C₁ C₂) F.∘ (to-⊎ C₁ C₂) ≗ F.id
    to∘from = [ (λ _ → refl) , (λ _ → refl) ]

module IndexedSum {i s p} {I : Set i} (C : I → Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ Σ I C ⟧ X ↔ (∃ λ i → ⟦ C i ⟧ X)
  correct {X = X} = mk↔ₛ′ (from-Σ I C) (to-Σ I C) (λ _ → refl) (λ _ → refl)

module ConstantExponentiation {i s p} {I : Set i} (C : Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ const[ I ]⟶ C ⟧ X ↔ (I → ⟦ C ⟧ X)
  correct = IndexedProduct.correct (F.const C)
