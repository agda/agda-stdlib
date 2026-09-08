------------------------------------------------------------------------
-- The Agda standard library
--
-- Container combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Combinator where

open import Data.Container.Core using (Container; Shape; Position; ⟦_⟧)
open import Data.Container.Relation.Unary.Any using (◇; any)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Product.Base as Product using (_,_; <_,_>; proj₁; proj₂; ∃)
open import Data.Sum.Base as Sum using ([_,_]′)
open import Data.Unit.Polymorphic.Base using (⊤)
import Function.Base as F
open import Level using (Level; _⊔_; lower)

------------------------------------------------------------------------
-- Combinators

module _ {s p : Level} where

-- Identity.

  id : Container s p
  id .Shape    = ⊤
  id .Position = F.const ⊤

  to-id : ∀ {a} {A : Set a} → F.id A → ⟦ id ⟧ A
  to-id x = (_ , λ _ → x)

  from-id : ∀ {a} {A : Set a} → ⟦ id ⟧ A → F.id A
  from-id xs = proj₂ xs _

-- Constant.

  const : Set s → Container s p
  const A .Shape    = A
  const A .Position = F.const ⊥

  to-const : ∀ {b} (A : Set s) {B : Set b} → A → ⟦ const A ⟧ B
  to-const _ = _, ⊥-elim {Whatever = F.const _}

  from-const : ∀ {b} (A : Set s) {B : Set b} → ⟦ const A ⟧ B → A
  from-const _ = proj₁

module _ {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

-- Composition.

  infixr 9 _∘_

  _∘_ : Container (s₁ ⊔ s₂ ⊔ p₁) (p₁ ⊔ p₂)
  _∘_ .Shape    = ⟦ C₁ ⟧ (Shape C₂)
  _∘_ .Position = ◇ C₁ (Position C₂)

  to-∘ : ∀ {a} {A : Set a} → ⟦ C₁ ⟧ (⟦ C₂ ⟧ A) → ⟦ _∘_ ⟧ A
  to-∘ (s , f) = ((s , proj₁ F.∘ f) , Product.uncurry (proj₂ F.∘ f) F.∘′ ◇.proof)

  from-∘ : ∀ {a} {A : Set a} → ⟦ _∘_ ⟧ A → ⟦ C₁ ⟧ (⟦ C₂ ⟧ A)
  from-∘ ((s , f) , g) = (s , < f , Product.curry (g F.∘′ any) >)

-- Product. (Note that, up to isomorphism, this is a special case of
-- indexed product.)

  infixr 2 _×_

  _×_ : Container (s₁ ⊔ s₂) (p₁ ⊔ p₂)
  _×_ .Shape    = Shape C₁ Product.× Shape C₂
  _×_ .Position = Product.uncurry λ s₁ s₂ → (Position C₁ s₁) Sum.⊎ (Position C₂ s₂)

  to-× : ∀ {a} {A : Set a} → ⟦ C₁ ⟧ A Product.× ⟦ C₂ ⟧ A → ⟦ _×_ ⟧ A
  to-× ((s₁ , f₁) , (s₂ , f₂)) = ((s₁ , s₂) , [ f₁ , f₂ ]′)

  from-× : ∀ {a} {A : Set a} → ⟦ _×_ ⟧ A → ⟦ C₁ ⟧ A Product.× ⟦ C₂ ⟧ A
  from-× ((s₁ , s₂) , f) = ((s₁ , f F.∘ Sum.inj₁) , (s₂ , f F.∘ Sum.inj₂))

-- Indexed product.

module _ {i s p} (I : Set i) (Cᵢ : I → Container s p) where

  Π : Container (i ⊔ s) (i ⊔ p)
  Π .Shape    = ∀ i → Shape (Cᵢ i)
  Π .Position = λ s → ∃ λ i → Position (Cᵢ i) (s i)

  to-Π : ∀ {a} {A : Set a} → (∀ i → ⟦ Cᵢ i ⟧ A) → ⟦ Π ⟧ A
  to-Π f = (proj₁ F.∘ f , Product.uncurry (proj₂ F.∘ f))

  from-Π : ∀ {a} {A : Set a} → ⟦ Π ⟧ A → ∀ i → ⟦ Cᵢ i ⟧ A
  from-Π (s , f) = λ i → (s i , λ p → f (i , p))

-- Constant exponentiation. (Note that this is a special case of
-- indexed product.)

infix 0 const[_]⟶_

const[_]⟶_ : ∀ {i s p} → Set i → Container s p → Container (i ⊔ s) (i ⊔ p)
const[ A ]⟶ C = Π A (F.const C)

-- Sum. (Note that, up to isomorphism, this is a special case of
-- indexed sum.)

module _ {s₁ s₂ p} (C₁ : Container s₁ p) (C₂ : Container s₂ p) where

  infixr 1 _⊎_

  _⊎_ : Container (s₁ ⊔ s₂) p
  _⊎_ .Shape    = (Shape C₁ Sum.⊎ Shape C₂)
  _⊎_ .Position = [ Position C₁ , Position C₂ ]′

  to-⊎ : ∀ {a} {A : Set a} → ⟦ C₁ ⟧ A Sum.⊎ ⟦ C₂ ⟧ A → ⟦ _⊎_ ⟧ A
  to-⊎ = [ Product.map Sum.inj₁ F.id , Product.map Sum.inj₂ F.id ]′

  from-⊎ : ∀ {a} {A : Set a} → ⟦ _⊎_ ⟧ A → ⟦ C₁ ⟧ A Sum.⊎ ⟦ C₂ ⟧ A
  from-⊎ (Sum.inj₁ s₁ , f) = Sum.inj₁ (s₁ , f)
  from-⊎ (Sum.inj₂ s₂ , f) = Sum.inj₂ (s₂ , f)

-- Indexed sum.

module _ {i s p} (I : Set i) (C : I → Container s p) where

  Σ : Container (i ⊔ s) p
  Σ .Shape    = ∃ λ i → Shape (C i)
  Σ .Position = λ s → Position (C (proj₁ s)) (proj₂ s)

  to-Σ : ∀ {a} {A : Set a} → (∃ λ i → ⟦ C i ⟧ A) → ⟦ Σ ⟧ A
  to-Σ (i , (s , f)) = ((i , s) , f)

  from-Σ : ∀ {a} {A : Set a} → ⟦ Σ ⟧ A → ∃ λ i → ⟦ C i ⟧ A
  from-Σ ((i , s) , f) = (i , (s , f))
