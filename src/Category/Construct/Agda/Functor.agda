------------------------------------------------------------------------
-- The Agda standard library
--
-- Functors in the agda category
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Category.Category
open import Category.Construct.Agda
open import Function
open import Relation.Binary.PropositionalEquality

-- these construction recover the old definitions of RawFunctor and Morphism
-- and provide a way to upgrade them to the generalized version

module Category.Construct.Agda.Functor {ℓ : Level} where

open import Category.Functor (agdaCat ℓ) (agdaCat ℓ)
  renaming (RawFunctor to RawFunctor′; RawMorphism to RawMorphism′)
open import Category.Structures (agdaCat ℓ)
  using (IsNatural)

record RawFunctor (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  infixl 4 _<$>_ _<$_
  infixl 1 _<&>_

  field
    _<$>_ : ∀ {A B} → (A → B) → F A → F B

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ y = const x <$> y

  _<&>_ : ∀ {A B} → F A → (A → B) → F B
  _<&>_ = flip _<$>_

  categoricalFunctor : RawFunctor′ F
  categoricalFunctor = record
    { fmap = _<$>_
    }

record Morphism {F₁ F₂ : Set ℓ → Set ℓ}
                (fun₁ : RawFunctor F₁)
                (fun₂ : RawFunctor F₂) : Set (suc ℓ) where
  open RawFunctor
  field
    op     : ∀{X} → F₁ X → F₂ X
    op-<$> : ∀{X Y} (f : X → Y) (x : F₁ X) →
           op (fun₁ ._<$>_ f x) ≡ fun₂ ._<$>_ f (op x)

  categorical : RawMorphism′ (categoricalFunctor fun₁) (categoricalFunctor fun₂)
  categorical = record
    { op = op
    }
  categorical-isNatural : IsNatural (agdaCat ℓ) categorical
  categorical-isNatural = record
    { op-<$> = op-<$>
    }
