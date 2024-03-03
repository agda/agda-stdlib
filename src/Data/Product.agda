------------------------------------------------------------------------
-- The Agda standard library
--
-- Products
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

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
-- Negation of existential quantifier

∄ : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄ P = ¬ ∃ P

-- Unique existence (parametrised by an underlying equality).

∃! : {A : Set a} → (A → A → Set ℓ) → (A → Set b) → Set (a ⊔ b ⊔ ℓ)
∃! _≈_ B = ∃ λ x → B x × (∀ {y} → B y → x ≈ y)

-- Syntax

infix 2 ∄-syntax

∄-syntax : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄-syntax = ∄

syntax ∄-syntax (λ x → B) = ∄[ x ] B
