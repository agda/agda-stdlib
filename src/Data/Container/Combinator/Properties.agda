------------------------------------------------------------------------
-- The Agda standard library
--
-- Correctness proofs for container combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Combinator.Properties where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Container.Core
open import Data.Container.Combinator
open import Data.Container.Relation.Unary.Any
open import Data.Empty using (⊥-elim)
open import Data.Product as Prod using (∃; _,_; proj₁; proj₂; <_,_>; uncurry; curry)
open import Data.Sum as S using (inj₁; inj₂; [_,_]′; [_,_])
open import Function as F using (_∘′_)
open import Function.Inverse as Inv using (_↔_; inverse; module Inverse)
open import Level using (_⊔_; lower)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)

-- I have proved some of the correctness statements under the
-- assumption of functional extensionality. I could have reformulated
-- the statements using suitable setoids, but I could not be bothered.

module Identity where

  correct : ∀ {s p x} {X : Set x} → ⟦ id {s} {p} ⟧ X ↔ F.id X
  correct {X = X} = inverse to from (λ _ → P.refl) (λ _ → P.refl)
    where
    to : ⟦ id ⟧ X → F.id X
    to xs = proj₂ xs _

    from : F.id X → ⟦ id ⟧ X
    from x = (_ , λ _ → x)

module Constant (ext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

  correct : ∀ {x p y} (X : Set x) {Y : Set y} → ⟦ const {x} {p ⊔ y} X ⟧ Y ↔ F.const X Y
  correct {x} {y} X {Y} = inverse proj₁ from from∘to λ _ → P.refl

    where
    from : X → ⟦ const X ⟧ Y
    from = < F.id , F.const (⊥-elim ∘′ lower) >

    from∘to : (x : ⟦ const X ⟧ Y) → from (proj₁ x) ≡ x
    from∘to xs = P.cong (proj₁ xs ,_) (ext (λ x → ⊥-elim (lower x)))

module Composition {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

  correct : ∀ {x} {X : Set x} → ⟦ C₁ ∘ C₂ ⟧ X ↔ (⟦ C₁ ⟧ F.∘ ⟦ C₂ ⟧) X
  correct {X = X} = inverse to from (λ _ → P.refl) (λ _ → P.refl)
    where
    to : ⟦ C₁ ∘ C₂ ⟧ X → ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)
    to ((s , f) , g) = (s , < f , curry (g ∘′ any) >)

    from : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X) → ⟦ C₁ ∘ C₂ ⟧ X
    from (s , f) = ((s , proj₁ F.∘ f) , uncurry (proj₂ F.∘ f) ∘′ ◇.proof)

module Product (ext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′)
       {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

  correct : ∀ {x} {X : Set x} →  ⟦ C₁ × C₂ ⟧ X ↔ (⟦ C₁ ⟧ X Prod.× ⟦ C₂ ⟧ X)
  correct {X = X} = inverse to from from∘to (λ _ → P.refl)
    where
    to : ⟦ C₁ × C₂ ⟧ X → ⟦ C₁ ⟧ X Prod.× ⟦ C₂ ⟧ X
    to ((s₁ , s₂) , f) = ((s₁ , f F.∘ inj₁) , (s₂ , f F.∘ inj₂))

    from : ⟦ C₁ ⟧ X Prod.× ⟦ C₂ ⟧ X → ⟦ C₁ × C₂ ⟧ X
    from ((s₁ , f₁) , (s₂ , f₂)) = ((s₁ , s₂) , [ f₁ , f₂ ]′)

    from∘to : from F.∘ to ≗ F.id
    from∘to (s , f) =
      P.cong (s ,_) (ext [ (λ _ → P.refl) , (λ _ → P.refl) ])

module IndexedProduct {i s p} {I : Set i} (Cᵢ : I → Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ Π I Cᵢ ⟧ X ↔ (∀ i → ⟦ Cᵢ i ⟧ X)
  correct {X = X} = inverse to from (λ _ → P.refl) (λ _ → P.refl)
    where
    to : ⟦ Π I Cᵢ ⟧ X → ∀ i → ⟦ Cᵢ i ⟧ X
    to (s , f) = λ i → (s i , λ p → f (i , p))

    from : (∀ i → ⟦ Cᵢ i ⟧ X) → ⟦ Π I Cᵢ ⟧ X
    from f = (proj₁ F.∘ f , uncurry (proj₂ F.∘ f))

module Sum {s₁ s₂ p} (C₁ : Container s₁ p) (C₂ : Container s₂ p) where

  correct : ∀ {x} {X : Set x} → ⟦ C₁ ⊎ C₂ ⟧ X ↔ (⟦ C₁ ⟧ X S.⊎ ⟦ C₂ ⟧ X)
  correct {X = X} = inverse to from from∘to to∘from
    where
    to : ⟦ C₁ ⊎ C₂ ⟧ X → ⟦ C₁ ⟧ X S.⊎ ⟦ C₂ ⟧ X
    to (inj₁ s₁ , f) = inj₁ (s₁ , f)
    to (inj₂ s₂ , f) = inj₂ (s₂ , f)

    from : ⟦ C₁ ⟧ X S.⊎ ⟦ C₂ ⟧ X → ⟦ C₁ ⊎ C₂ ⟧ X
    from = [ Prod.map inj₁ F.id , Prod.map inj₂ F.id ]′

    from∘to : from F.∘ to ≗ F.id
    from∘to (inj₁ s₁ , f) = P.refl
    from∘to (inj₂ s₂ , f) = P.refl

    to∘from : to F.∘ from ≗ F.id
    to∘from = [ (λ _ → P.refl) , (λ _ → P.refl) ]

module IndexedSum {i s p} {I : Set i} (C : I → Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ Σ I C ⟧ X ↔ (∃ λ i → ⟦ C i ⟧ X)
  correct {X = X} = inverse to from (λ _ → P.refl) (λ _ → P.refl)
    where
    to : ⟦ Σ I C ⟧ X → ∃ λ i → ⟦ C i ⟧ X
    to ((i , s) , f) = (i , (s , f))

    from : (∃ λ i → ⟦ C i ⟧ X) → ⟦ Σ I C ⟧ X
    from (i , (s , f)) = ((i , s) , f)

module ConstantExponentiation {i s p} {I : Set i} (C : Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ const[ I ]⟶ C ⟧ X ↔ (I → ⟦ C ⟧ X)
  correct = IndexedProduct.correct (F.const C)
