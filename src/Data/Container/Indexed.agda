------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed containers aka interaction structures aka polynomial
-- functors. The notation and presentation here is closest to that of
-- Hancock and Hyvernat in "Programming interfaces and basic topology"
-- (2006/9).
--
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Indexed where

open import Level
open import Codata.Musical.M.Indexed
open import Data.Product as Prod hiding (map)
open import Data.W.Indexed
open import Function renaming (id to ⟨id⟩; _∘_ to _⟨∘⟩_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (_↔_; module Inverse)
open import Relation.Unary using (Pred; _⊆_)
import Relation.Binary as B
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_; refl)

------------------------------------------------------------------------

-- The type and its semantics ("extension").

open import Data.Container.Indexed.Core public
open Container public

-- Abbreviation for the commonly used level one version of indexed
-- containers.

_▷_ : Set → Set → Set₁
I ▷ O = Container I O zero zero

-- The least and greatest fixpoint.

μ ν : ∀ {o c r} {O : Set o} → Container O O c r → Pred O _
μ = W
ν = M

-- An equivalence relation is defined in Data.Container.Indexed.WithK.

------------------------------------------------------------------------
-- Functoriality

-- Indexed containers are functors.

map : ∀ {i o c r ℓ₁ ℓ₂} {I : Set i} {O : Set o}
      (C : Container I O c r) {X : Pred I ℓ₁} {Y : Pred I ℓ₂} →
      X ⊆ Y → ⟦ C ⟧ X ⊆ ⟦ C ⟧ Y
map _ f = Prod.map ⟨id⟩ (λ g → f ⟨∘⟩ g)

-- Some properties are proved in Data.Container.Indexed.WithK.

------------------------------------------------------------------------
-- Container morphisms

module _ {i₁ i₂ o₁ o₂}
         {I₁ : Set i₁} {I₂ : Set i₂} {O₁ : Set o₁} {O₂ : Set o₂} where

  -- General container morphism.

  record ContainerMorphism {c₁ c₂ r₁ r₂ ℓ₁ ℓ₂}
         (C₁ : Container I₁ O₁ c₁ r₁) (C₂ : Container I₂ O₂ c₂ r₂)
         (f : I₁ → I₂) (g : O₁ → O₂)
         (_∼_ : B.Rel I₂ ℓ₁) (_≈_ : B.REL (Set r₂) (Set r₁) ℓ₂)
         (_·_ : ∀ {A B} → A ≈ B → A → B) :
         Set (i₁ ⊔ i₂ ⊔ o₁ ⊔ o₂ ⊔ c₁ ⊔ c₂ ⊔ r₁ ⊔ r₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      command   : Command C₁ ⊆ Command C₂ ⟨∘⟩ g
      response  : ∀ {o} {c₁ : Command C₁ o} →
                  Response C₂ (command c₁) ≈ Response C₁ c₁
      coherent  : ∀ {o} {c₁ : Command C₁ o} {r₂ : Response C₂ (command c₁)} →
                  f (next C₁ c₁ (response · r₂)) ∼ next C₂ (command c₁) r₂

  open ContainerMorphism public

  -- Plain container morphism.

  _⇒[_/_]_ : ∀ {c₁ c₂ r₁ r₂} →
             Container I₁ O₁ c₁ r₁ → (I₁ → I₂) → (O₁ → O₂) →
             Container I₂ O₂ c₂ r₂ → Set _
  C₁ ⇒[ f / g ] C₂ = ContainerMorphism C₁ C₂ f g _≡_ (λ R₂ R₁ → R₂ → R₁) _$_

  -- Linear container morphism.

  _⊸[_/_]_ : ∀ {c₁ c₂ r₁ r₂} →
             Container I₁ O₁ c₁ r₁ → (I₁ → I₂) → (O₁ → O₂) →
             Container I₂ O₂ c₂ r₂ → Set _
  C₁ ⊸[ f / g ] C₂ = ContainerMorphism C₁ C₂ f g _≡_ _↔_
                                       (λ r₂↔r₁ r₂ → Inverse.to r₂↔r₁ ⟨$⟩ r₂)

  -- Cartesian container morphism.

  _⇒C[_/_]_ : ∀ {c₁ c₂ r} →
              Container I₁ O₁ c₁ r → (I₁ → I₂) → (O₁ → O₂) →
              Container I₂ O₂ c₂ r → Set _
  C₁ ⇒C[ f / g ] C₂ = ContainerMorphism C₁ C₂ f g _≡_ (λ R₂ R₁ → R₂ ≡ R₁)
                                        (λ r₂≡r₁ r₂ → P.subst ⟨id⟩ r₂≡r₁ r₂)

-- Degenerate cases where no reindexing is performed.

module _ {i o c r} {I : Set i} {O : Set o} where

  _⇒_ : B.Rel (Container I O c r) _
  C₁ ⇒ C₂ = C₁ ⇒[ ⟨id⟩ / ⟨id⟩ ] C₂

  _⊸_ : B.Rel (Container I O c r) _
  C₁ ⊸ C₂ = C₁ ⊸[ ⟨id⟩ / ⟨id⟩ ] C₂

  _⇒C_ : B.Rel (Container I O c r) _
  C₁ ⇒C C₂ = C₁ ⇒C[ ⟨id⟩ / ⟨id⟩ ] C₂

------------------------------------------------------------------------
-- Plain morphisms

-- Interpretation of _⇒_.

⟪_⟫ : ∀ {i o c r ℓ} {I : Set i} {O : Set o} {C₁ C₂ : Container I O c r} →
      C₁ ⇒ C₂ → (X : Pred I ℓ) → ⟦ C₁ ⟧ X ⊆ ⟦ C₂ ⟧ X
⟪ m ⟫ X (c , k) = command m c , λ r₂ →
  P.subst X (coherent m) (k (response m r₂))

module PlainMorphism {i o c r} {I : Set i} {O : Set o} where

  -- Identity.

  id : (C : Container I O c r) → C ⇒ C
  id _ = record
    { command  = ⟨id⟩
    ; response = ⟨id⟩
    ; coherent = refl
    }

  -- Composition.

  infixr 9 _∘_

  _∘_ : {C₁ C₂ C₃ : Container I O c r} →
        C₂ ⇒ C₃ → C₁ ⇒ C₂ → C₁ ⇒ C₃
  f ∘ g = record
    { command  = command  f ⟨∘⟩ command g
    ; response = response g ⟨∘⟩ response f
    ; coherent = coherent g ⟨ P.trans ⟩ coherent f
    }

  -- Identity commutes with ⟪_⟫.

  id-correct : ∀ {ℓ} {C : Container I O c r} → ∀ {X : Pred I ℓ} {o} →
               ⟪ id C ⟫ X {o} ≗ ⟨id⟩
  id-correct _ = refl

  -- More properties are proved in Data.Container.Indexed.WithK.

------------------------------------------------------------------------
-- Linear container morphisms

module LinearMorphism
  {i o c r} {I : Set i} {O : Set o} {C₁ C₂ : Container I O c r}
  (m : C₁ ⊸ C₂)
  where

  morphism : C₁ ⇒ C₂
  morphism = record
    { command  = command m
    ; response = _⟨$⟩_ (Inverse.to (response m))
    ; coherent = coherent m
    }

  ⟪_⟫⊸ : ∀ {ℓ} (X : Pred I ℓ) → ⟦ C₁ ⟧ X ⊆ ⟦ C₂ ⟧ X
  ⟪_⟫⊸ = ⟪ morphism ⟫

open LinearMorphism public using (⟪_⟫⊸)

------------------------------------------------------------------------
-- Cartesian morphisms

module CartesianMorphism
  {i o c r} {I : Set i} {O : Set o} {C₁ C₂ : Container I O c r}
  (m : C₁ ⇒C C₂)
  where

  morphism : C₁ ⇒ C₂
  morphism = record
    { command  = command m
    ; response = P.subst ⟨id⟩ (response m)
    ; coherent = coherent m
    }

  ⟪_⟫C : ∀ {ℓ} (X : Pred I ℓ) → ⟦ C₁ ⟧ X ⊆ ⟦ C₂ ⟧ X
  ⟪_⟫C = ⟪ morphism ⟫

open CartesianMorphism public using (⟪_⟫C)

------------------------------------------------------------------------
-- All and any

-- □ and ◇ are defined in the core module.

module _ {i o c r ℓ₁ ℓ₂} {I : Set i} {O : Set o} (C : Container I O c r)
         {X : Pred I ℓ₁} {P Q : Pred (Σ I X) ℓ₂} where

  -- All.

  □-map : P ⊆ Q → □ C P ⊆ □ C Q
  □-map P⊆Q = _⟨∘⟩_ P⊆Q

  -- Any.

  ◇-map : P ⊆ Q → ◇ C P ⊆ ◇ C Q
  ◇-map P⊆Q = Prod.map ⟨id⟩ P⊆Q

-- Membership is defined in Data.Container.Indexed.WithK.
