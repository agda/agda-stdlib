------------------------------------------------------------------------
-- The Agda standard library
--
-- Container combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Combinator where

open import Level using (Level; _⊔_; Lift)
open import Data.Empty using (⊥)
open import Data.Product as P using (_,_; proj₁; proj₂; ∃)
open import Data.Sum.Base as S using ([_,_]′)
open import Data.Unit.Base using (⊤)
import Function as F

open import Data.Container.Core
open import Data.Container.Relation.Unary.Any

------------------------------------------------------------------------
-- Combinators

module _ {s p : Level} where

-- Identity.

  id : Container s p
  id .Shape    = Lift s ⊤
  id .Position = F.const (Lift p ⊤)

-- Constant.

  const : Set s → Container s p
  const X .Shape    = X
  const X .Position = F.const (Lift p ⊥)

-- Composition.

infixr 9 _∘_

_∘_ : ∀ {s₁ s₂ p₁ p₂} → Container s₁ p₁ → Container s₂ p₂ →
      Container (s₁ ⊔ s₂ ⊔ p₁) (p₁ ⊔ p₂)
(C₁ ∘ C₂) .Shape    = ⟦ C₁ ⟧ (Shape C₂)
(C₁ ∘ C₂) .Position = ◇ C₁ (Position C₂)

-- Product. (Note that, up to isomorphism, this is a special case of
-- indexed product.)

infixr 2 _×_

_×_ : ∀ {s₁ s₂ p₁ p₂} → Container s₁ p₁ → Container s₂ p₂ →
      Container (s₁ ⊔ s₂) (p₁ ⊔ p₂)
(C₁ × C₂) .Shape    = Shape C₁ P.× Shape C₂
(C₁ × C₂) .Position = P.uncurry λ s₁ s₂ → (Position C₁ s₁) S.⊎ (Position C₂ s₂)

-- Indexed product.

Π : ∀ {i s p} (I : Set i) → (I → Container s p) → Container (i ⊔ s) (i ⊔ p)
Π I C .Shape    = ∀ i → Shape (C i)
Π I C .Position = λ s → ∃ λ i → Position (C i) (s i)

-- Constant exponentiation. (Note that this is a special case of
-- indexed product.)

infix 0 const[_]⟶_

const[_]⟶_ : ∀ {i s p} → Set i → Container s p → Container (i ⊔ s) (i ⊔ p)
const[ X ]⟶ C = Π X (F.const C)

-- Sum. (Note that, up to isomorphism, this is a special case of
-- indexed sum.)

infixr 1 _⊎_

_⊎_ : ∀ {s₁ s₂ p} → Container s₁ p → Container s₂ p → Container (s₁ ⊔ s₂) p
(C₁ ⊎ C₂) .Shape    = (Shape C₁ S.⊎ Shape C₂)
(C₁ ⊎ C₂) .Position = [ Position C₁ , Position C₂ ]′

-- Indexed sum.

Σ : ∀ {i s p} (I : Set i) → (I → Container s p) → Container (i ⊔ s) p
Σ I C .Shape    = ∃ λ i → Shape (C i)
Σ I C .Position = λ s → Position (C (proj₁ s)) (proj₂ s)
