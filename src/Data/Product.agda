------------------------------------------------------------------------
-- The Agda standard library
--
-- Products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product where

open import Function.Base
open import Level
open import Relation.Nullary.Negation.Core

private
  variable
    a b c ℓ : Level
    A B : Set a

------------------------------------------------------------------------
-- Definition of dependent products

open import Data.Product.Base public

------------------------------------------------------------------------
-- Existential quantifiers

∃ : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∄ : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄ P = ¬ ∃ P

∃₂ : ∀ {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b

-- Unique existence (parametrised by an underlying equality).

∃! : {A : Set a} → (A → A → Set ℓ) → (A → Set b) → Set (a ⊔ b ⊔ ℓ)
∃! _≈_ B = ∃ λ x → B x × (∀ {y} → B y → x ≈ y)

-- Syntax

infix 2 ∃-syntax

∃-syntax : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B

infix 2 ∄-syntax

∄-syntax : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄-syntax = ∄

syntax ∄-syntax (λ x → B) = ∄[ x ] B
