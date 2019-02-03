------------------------------------------------------------------------
-- The Agda standard library
--
-- Container combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Data.Container.Combinator where

open import Data.Container
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product as Prod hiding (Σ) renaming (_×_ to _⟨×⟩_)
open import Data.Sum renaming (_⊎_ to _⟨⊎⟩_)
open import Data.Unit.Base using (⊤)
open import Function as F hiding (id; const) renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse using (_↔_; inverse)
open import Level
open import Relation.Binary.PropositionalEquality as P using (_≗_; _≡_)

------------------------------------------------------------------------
-- Combinators

module _ {s p : Level} where

-- Identity.

  id : Container s p
  id = Lift s ⊤ ▷ F.const (Lift p ⊤)

-- Constant.

  const : Set s → Container s p
  const X = X ▷ F.const (Lift p ⊥)

-- Composition.

infixr 9 _∘_

_∘_ : ∀ {s₁ s₂ p₁ p₂} → Container s₁ p₁ → Container s₂ p₂ → Container (s₁ ⊔ s₂ ⊔ p₁) (p₁ ⊔ p₂)
C₁ ∘ C₂ = ⟦ C₁ ⟧ (Shape C₂) ▷ ◇ (Position C₂)

-- Product. (Note that, up to isomorphism, this is a special case of
-- indexed product.)

infixr 2 _×_

_×_ : ∀ {s₁ s₂ p₁ p₂} → Container s₁ p₁ → Container s₂ p₂ → Container (s₁ ⊔ s₂) (p₁ ⊔ p₂)
C₁ × C₂ =
  (Shape C₁ ⟨×⟩ Shape C₂) ▷
  uncurry (λ s₁ s₂ → Position C₁ s₁ ⟨⊎⟩ Position C₂ s₂)

-- Indexed product.

Π : ∀ {i s p} {I : Set i} → (I → Container s p) → Container (i ⊔ s) (i ⊔ p)
Π C = (∀ i → Shape (C i)) ▷ λ s → ∃ λ i → Position (C i) (s i)

-- Sum. (Note that, up to isomorphism, this is a special case of
-- indexed sum.)

infixr 1 _⊎_

_⊎_ : ∀ {s₁ s₂ p} → Container s₁ p → Container s₂ p → Container (s₁ ⊔ s₂) p
C₁ ⊎ C₂ = (Shape C₁ ⟨⊎⟩ Shape C₂) ▷ [ Position C₁ , Position C₂ ]

-- Indexed sum.

Σ : ∀ {i s p} {I : Set i} → (I → Container s p) → Container (i ⊔ s) p
Σ C = (∃ λ i → Shape (C i)) ▷ λ s → Position (C (proj₁ s)) (proj₂ s)

-- Constant exponentiation. (Note that this is a special case of
-- indexed product.)

infix 0 const[_]⟶_

const[_]⟶_ : ∀ {i s p} → Set i → Container s p → Container (i ⊔ s) (i ⊔ p)
const[ X ]⟶ C = Π {I = X} (F.const C)

------------------------------------------------------------------------
-- Correctness proofs

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

module Constant (ext : ∀ {ℓ ℓ′} → P.Extensionality ℓ ℓ′) where

  correct : ∀ {x p y} (X : Set x) {Y : Set y} → ⟦ const {x} {p ⊔ y} X ⟧ Y ↔ F.const X Y
  correct {x} {y} X {Y} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { right-inverse-of = λ _ → P.refl
      ; left-inverse-of  = from∘to
      }
    }
    where
    to : ⟦ const X ⟧ Y → X
    to = proj₁

    from : X → ⟦ const X ⟧ Y
    from = < F.id , F.const (⊥-elim ∘′ lower) >

    from∘to : (x : ⟦ const X ⟧ Y) → from (to x) ≡ x
    from∘to xs = P.cong (proj₁ xs ,_) (ext (λ x → ⊥-elim (lower x)))

module Composition {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

  correct : ∀ {x} {X : Set x} → ⟦ C₁ ∘ C₂ ⟧ X ↔ (⟦ C₁ ⟧ ⟨∘⟩ ⟦ C₂ ⟧) X
  correct {X = X} = inverse to from (λ _ → P.refl) (λ _ → P.refl)
    where
    to : ⟦ C₁ ∘ C₂ ⟧ X → ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)
    to ((s , f) , g) = (s , < f , curry g >)

    from : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X) → ⟦ C₁ ∘ C₂ ⟧ X
    from (s , f) = ((s , proj₁ ⟨∘⟩ f) , uncurry (proj₂ ⟨∘⟩ f))

module Product (ext : ∀ {ℓ ℓ′} → P.Extensionality ℓ ℓ′)
       {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

  correct : ∀ {x} {X : Set x} →  ⟦ C₁ × C₂ ⟧ X ↔ (⟦ C₁ ⟧ X ⟨×⟩ ⟦ C₂ ⟧ X)
  correct {X = X} = inverse to from from∘to (λ _ → P.refl)
    where
    to : ⟦ C₁ × C₂ ⟧ X → ⟦ C₁ ⟧ X ⟨×⟩ ⟦ C₂ ⟧ X
    to ((s₁ , s₂) , f) = ((s₁ , f ⟨∘⟩ inj₁) , (s₂ , f ⟨∘⟩ inj₂))

    from : ⟦ C₁ ⟧ X ⟨×⟩ ⟦ C₂ ⟧ X → ⟦ C₁ × C₂ ⟧ X
    from ((s₁ , f₁) , (s₂ , f₂)) = ((s₁ , s₂) , [ f₁ , f₂ ])

    from∘to : from ⟨∘⟩ to ≗ F.id
    from∘to (s , f) =
      P.cong (s ,_) (ext [ (λ _ → P.refl) , (λ _ → P.refl) ])

module IndexedProduct {i s p} {I : Set i} (Cᵢ : I → Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ Π Cᵢ ⟧ X ↔ (∀ i → ⟦ Cᵢ i ⟧ X)
  correct {X = X} = inverse to from (λ _ → P.refl) (λ _ → P.refl)
    where
    to : ⟦ Π Cᵢ ⟧ X → ∀ i → ⟦ Cᵢ i ⟧ X
    to (s , f) = λ i → (s i , λ p → f (i , p))

    from : (∀ i → ⟦ Cᵢ i ⟧ X) → ⟦ Π Cᵢ ⟧ X
    from f = (proj₁ ⟨∘⟩ f , uncurry (proj₂ ⟨∘⟩ f))

module Sum {s₁ s₂ p} (C₁ : Container s₁ p) (C₂ : Container s₂ p) where

  correct : ∀ {x} {X : Set x} → ⟦ C₁ ⊎ C₂ ⟧ X ↔ (⟦ C₁ ⟧ X ⟨⊎⟩ ⟦ C₂ ⟧ X)
  correct {X = X} = inverse to from from∘to to∘from
    where
    to : ⟦ C₁ ⊎ C₂ ⟧ X → ⟦ C₁ ⟧ X ⟨⊎⟩ ⟦ C₂ ⟧ X
    to (inj₁ s₁ , f) = inj₁ (s₁ , f)
    to (inj₂ s₂ , f) = inj₂ (s₂ , f)

    from : ⟦ C₁ ⟧ X ⟨⊎⟩ ⟦ C₂ ⟧ X → ⟦ C₁ ⊎ C₂ ⟧ X
    from = [ Prod.map inj₁ F.id , Prod.map inj₂ F.id ]

    from∘to : from ⟨∘⟩ to ≗ F.id
    from∘to (inj₁ s₁ , f) = P.refl
    from∘to (inj₂ s₂ , f) = P.refl

    to∘from : to ⟨∘⟩ from ≗ F.id
    to∘from = [ (λ _ → P.refl) , (λ _ → P.refl) ]

module IndexedSum {i s p} {I : Set i} (C : I → Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ Σ C ⟧ X ↔ (∃ λ i → ⟦ C i ⟧ X)
  correct {X = X} = inverse to from (λ _ → P.refl) (λ _ → P.refl)
    where
    to : ⟦ Σ C ⟧ X → ∃ λ i → ⟦ C i ⟧ X
    to ((i , s) , f) = (i , (s , f))

    from : (∃ λ i → ⟦ C i ⟧ X) → ⟦ Σ C ⟧ X
    from (i , (s , f)) = ((i , s) , f)

module ConstantExponentiation {i s p} {I : Set i} (C : Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ const[ I ]⟶ C ⟧ X ↔ (I → ⟦ C ⟧ X)
  correct = IndexedProduct.correct (F.const C)
