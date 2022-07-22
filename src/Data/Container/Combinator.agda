------------------------------------------------------------------------
-- The Agda standard library
--
-- Container combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Combinator where

open import Level using (Level; _⊔_; lower)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Product as P using (_,_; <_,_>; proj₁; proj₂; ∃)
open import Data.Sum.Base as S using ([_,_]′)
open import Data.Unit.Polymorphic.Base using (⊤)
import Function as F

open import Data.Container.Core
open import Data.Container.Relation.Unary.Any

------------------------------------------------------------------------
-- Combinators

module _ {s p : Level} where

-- Identity.

  id : Container s p
  id .Shape    = ⊤
  id .Position = F.const ⊤

  to-id : ∀ {x} {X : Set x} → F.id X → ⟦ id ⟧ X
  to-id x = (_ , λ _ → x)

  from-id : ∀ {x} {X : Set x} → ⟦ id ⟧ X → F.id X
  from-id xs = proj₂ xs _

-- Constant.

  const : Set s → Container s p
  const X .Shape    = X
  const X .Position = F.const ⊥

  to-const : ∀ {y} (X : Set s) {Y : Set y} → X → ⟦ const X ⟧ Y
  to-const _ = _, ⊥-elim {Whatever = F.const _}

  from-const : ∀ {y} (X : Set s) {Y : Set y} → ⟦ const X ⟧ Y → X
  from-const _ = proj₁

module _ {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

-- Composition.

  infixr 9 _∘_

  _∘_ : Container (s₁ ⊔ s₂ ⊔ p₁) (p₁ ⊔ p₂)
  _∘_ .Shape    = ⟦ C₁ ⟧ (Shape C₂)
  _∘_ .Position = ◇ C₁ (Position C₂)

  to-_∘_ : ∀ {x} {X : Set x} → ⟦ C₁ ⟧ (⟦ C₂ ⟧ X) → ⟦ _∘_ ⟧ X
  to-_∘_ (s , f) = ((s , proj₁ F.∘ f) , P.uncurry (proj₂ F.∘ f) F.∘′ ◇.proof)

  from-_∘_ : ∀ {x} {X : Set x} → ⟦ _∘_ ⟧ X → ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)
  from-_∘_ ((s , f) , g) = (s , < f , P.curry (g F.∘′ any) >)

-- Product. (Note that, up to isomorphism, this is a special case of
-- indexed product.)

  infixr 2 _×_

  _×_ : Container (s₁ ⊔ s₂) (p₁ ⊔ p₂)
  _×_ .Shape    = Shape C₁ P.× Shape C₂
  _×_ .Position = P.uncurry λ s₁ s₂ → (Position C₁ s₁) S.⊎ (Position C₂ s₂)

  to-_×_ : ∀ {x} {X : Set x} → ⟦ C₁ ⟧ X P.× ⟦ C₂ ⟧ X → ⟦ _×_ ⟧ X
  to-_×_ ((s₁ , f₁) , (s₂ , f₂)) = ((s₁ , s₂) , [ f₁ , f₂ ]′)

  from-_×_ : ∀ {x} {X : Set x} → ⟦ _×_ ⟧ X → ⟦ C₁ ⟧ X P.× ⟦ C₂ ⟧ X
  from-_×_ ((s₁ , s₂) , f) = ((s₁ , f F.∘ S.inj₁) , (s₂ , f F.∘ S.inj₂))

-- Indexed product.

module _ {i s p} (I : Set i) (Cᵢ : I → Container s p) where

  Π : Container (i ⊔ s) (i ⊔ p)
  Π .Shape    = ∀ i → Shape (Cᵢ i)
  Π .Position = λ s → ∃ λ i → Position (Cᵢ i) (s i)

  to-Π : ∀ {x} {X : Set x} → (∀ i → ⟦ Cᵢ i ⟧ X) → ⟦ Π ⟧ X
  to-Π f = (proj₁ F.∘ f , P.uncurry (proj₂ F.∘ f))

  from-Π : ∀ {x} {X : Set x} → ⟦ Π ⟧ X → ∀ i → ⟦ Cᵢ i ⟧ X
  from-Π (s , f) = λ i → (s i , λ p → f (i , p))

-- Constant exponentiation. (Note that this is a special case of
-- indexed product.)

infix 0 const[_]⟶_

const[_]⟶_ : ∀ {i s p} → Set i → Container s p → Container (i ⊔ s) (i ⊔ p)
const[ X ]⟶ C = Π X (F.const C)

-- Sum. (Note that, up to isomorphism, this is a special case of
-- indexed sum.)

module _ {s₁ s₂ p} (C₁ : Container s₁ p) (C₂ : Container s₂ p) where
  
  infixr 1 _⊎_

  _⊎_ : Container (s₁ ⊔ s₂) p
  _⊎_ .Shape    = (Shape C₁ S.⊎ Shape C₂)
  _⊎_ .Position = [ Position C₁ , Position C₂ ]′

  to-_⊎_ : ∀ {x} {X : Set x} → ⟦ C₁ ⟧ X S.⊎ ⟦ C₂ ⟧ X → ⟦ _⊎_ ⟧ X
  to-_⊎_ = [ P.map S.inj₁ F.id , P.map S.inj₂ F.id ]′

  from-_⊎_ : ∀ {x} {X : Set x} → ⟦ _⊎_ ⟧ X → ⟦ C₁ ⟧ X S.⊎ ⟦ C₂ ⟧ X
  from-_⊎_ (S.inj₁ s₁ , f) = S.inj₁ (s₁ , f)
  from-_⊎_ (S.inj₂ s₂ , f) = S.inj₂ (s₂ , f)

-- Indexed sum.

module _ {i s p} (I : Set i) (C : I → Container s p) where

  Σ : Container (i ⊔ s) p
  Σ .Shape    = ∃ λ i → Shape (C i)
  Σ .Position = λ s → Position (C (proj₁ s)) (proj₂ s)

  to-Σ : ∀ {x} {X : Set x} → (∃ λ i → ⟦ C i ⟧ X) → ⟦ Σ ⟧ X
  to-Σ (i , (s , f)) = ((i , s) , f)

  from-Σ : ∀ {x} {X : Set x} → ⟦ Σ ⟧ X → ∃ λ i → ⟦ C i ⟧ X
  from-Σ ((i , s) , f) = (i , (s , f))
