------------------------------------------------------------------------
-- The Agda standard library
--
-- A module used for creating function pipelines, see
-- README.Function.Reasoning for examples
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Reasoning where

open import Function.Base using (_∋_; _∘_)

-- Need to give _∋_ a new name as syntax cannot contain underscores
infixl 0 ∋-syntax
∋-syntax = _∋_

-- Create ∶ syntax
syntax ∋-syntax A a = a ∶ A

-- Export pipeline functions
open import Function public using (_|>_; _|>′_)



module ≗-Reasoning {ℓ₁} {ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} where
  open import Relation.Binary using (Setoid)
  open import Relation.Binary.PropositionalEquality using (_≡_; cong; _→-setoid_; _≗_)
  open import Relation.Binary.Reasoning.Setoid (A →-setoid B) public
  open Setoid (A →-setoid B) using (refl; trans)

  infix  1 on_begin_
  infix  5 _∘>_
  infixr 4 _⟩∘⟨_

  on_begin_ : {f g : A → B} → (a : A) → f IsRelatedTo g → f a ≡ g a
  on a begin P = (begin P) a

  _∘>_ : ∀ {ℓ} {C : Set ℓ} {g h : A → C} (f : C → B) (gh : g ≗ h) → f ∘ g ≗ f ∘ h
  f ∘> gh = (cong f) ∘ gh

  _⟩∘⟨_ : ∀ {ℓ} {C : Set ℓ} {f f′ : C → B} {g g′ : A → C} → f ≗ f′ → g ≗ g′ → f ∘ g ≗ f′ ∘ g′
  _⟩∘⟨_ {f′ = f′} {g} ff′ gg′ = trans (ff′ ∘ g) (f′ ∘> gg′)

  ≗-refl = refl
