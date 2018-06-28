------------------------------------------------------------------------
-- The Agda standard library
--
-- Container combinators
------------------------------------------------------------------------

module Data.Container.Combinator where

open import Data.Container
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product as Prod hiding (Σ) renaming (_×_ to _⟨×⟩_)
open import Data.Sum renaming (_⊎_ to _⟨⊎⟩_)
open import Data.Unit.Base using (⊤)
open import Function as F hiding (id; const) renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse using (_↔_)
open import Level
open import Relation.Binary.PropositionalEquality as P
  using (_≗_; refl)

------------------------------------------------------------------------
-- Combinators

-- Identity.

id : ∀ {s p} → Container s p
id = Lift ⊤ ▷ F.const (Lift ⊤)

-- Constant.

const : ∀ {s p} → Set s → Container s p
const X = X ▷ F.const (Lift ⊥)

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
  correct  = record
    { to         = P.→-to-⟶ λ xs → proj₂ xs _
    ; from       = P.→-to-⟶ λ x → (_ , λ _ → x)
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }

module Constant (ext : ∀ {ℓ ℓ′} → P.Extensionality ℓ ℓ′) where


  correct : ∀ {x p y} (X : Set x) {Y : Set y} → ⟦ const {x} {p ⊔ y} X ⟧ Y ↔ F.const X Y
  correct {x} {y} X {Y} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { right-inverse-of = λ _ → refl
      ; left-inverse-of  =
          λ xs → P.cong (_,_ (proj₁ xs)) (ext (λ x → ⊥-elim (lower x)))
      }
    } where

    to : ⟦ const X ⟧ Y → X
    to = proj₁

    from : X → ⟦ const X ⟧ Y
    from = < F.id , F.const (⊥-elim ∘′ lower) >

module Composition {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

  correct : ∀ {x} {X : Set x} → ⟦ C₁ ∘ C₂ ⟧ X ↔ (⟦ C₁ ⟧ ⟨∘⟩ ⟦ C₂ ⟧) X
  correct {X = X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ C₁ ∘ C₂ ⟧ X → ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)
    to ((s , f) , g) = (s , < f , curry g >)

    from : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X) → ⟦ C₁ ∘ C₂ ⟧ X
    from (s , f) = ((s , proj₁ ⟨∘⟩ f) , uncurry (proj₂ ⟨∘⟩ f))

module Product (ext : ∀ {ℓ ℓ′} → P.Extensionality ℓ ℓ′)
       {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

  correct : ∀ {x} {X : Set x} →  ⟦ C₁ × C₂ ⟧ X ↔ (⟦ C₁ ⟧ X ⟨×⟩ ⟦ C₂ ⟧ X)
  correct {X = X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ C₁ × C₂ ⟧ X → ⟦ C₁ ⟧ X ⟨×⟩ ⟦ C₂ ⟧ X
    to ((s₁ , s₂) , f) = ((s₁ , f ⟨∘⟩ inj₁) , (s₂ , f ⟨∘⟩ inj₂))

    from : ⟦ C₁ ⟧ X ⟨×⟩ ⟦ C₂ ⟧ X → ⟦ C₁ × C₂ ⟧ X
    from ((s₁ , f₁) , (s₂ , f₂)) = ((s₁ , s₂) , [ f₁ , f₂ ])

    from∘to : from ⟨∘⟩ to ≗ F.id
    from∘to (s , f) =
      P.cong (_,_ s) (ext [ (λ _ → refl) , (λ _ → refl) ])

module IndexedProduct {i s p} {I : Set i} (Cᵢ : I → Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ Π Cᵢ ⟧ X ↔ (∀ i → ⟦ Cᵢ i ⟧ X)
  correct {X = X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ Π Cᵢ ⟧ X → ∀ i → ⟦ Cᵢ i ⟧ X
    to (s , f) = λ i → (s i , λ p → f (i , p))

    from : (∀ i → ⟦ Cᵢ i ⟧ X) → ⟦ Π Cᵢ ⟧ X
    from f = (proj₁ ⟨∘⟩ f , uncurry (proj₂ ⟨∘⟩ f))

module Sum {s₁ s₂ p} (C₁ : Container s₁ p) (C₂ : Container s₂ p) where

  correct : ∀ {x} {X : Set x} → ⟦ C₁ ⊎ C₂ ⟧ X ↔ (⟦ C₁ ⟧ X ⟨⊎⟩ ⟦ C₂ ⟧ X)
  correct {X = X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = [ (λ _ → refl) , (λ _ → refl) ]
      }
    }
    where
    to : ⟦ C₁ ⊎ C₂ ⟧ X → ⟦ C₁ ⟧ X ⟨⊎⟩ ⟦ C₂ ⟧ X
    to (inj₁ s₁ , f) = inj₁ (s₁ , f)
    to (inj₂ s₂ , f) = inj₂ (s₂ , f)

    from : ⟦ C₁ ⟧ X ⟨⊎⟩ ⟦ C₂ ⟧ X → ⟦ C₁ ⊎ C₂ ⟧ X
    from = [ Prod.map inj₁ F.id , Prod.map inj₂ F.id ]

    from∘to : from ⟨∘⟩ to ≗ F.id
    from∘to (inj₁ s₁ , f) = refl
    from∘to (inj₂ s₂ , f) = refl

module IndexedSum {i s p} {I : Set i} (C : I → Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ Σ C ⟧ X ↔ (∃ λ i → ⟦ C i ⟧ X)
  correct {X = X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ Σ C ⟧ X → ∃ λ i → ⟦ C i ⟧ X
    to ((i , s) , f) = (i , (s , f))

    from : (∃ λ i → ⟦ C i ⟧ X) → ⟦ Σ C ⟧ X
    from (i , (s , f)) = ((i , s) , f)

module ConstantExponentiation {i s p} {I : Set i} (C : Container s p) where

  correct : ∀ {x} {X : Set x} → ⟦ const[ I ]⟶ C ⟧ X ↔ (I → ⟦ C ⟧ X)
  correct = IndexedProduct.correct (F.const C)
