------------------------------------------------------------------------
-- The Agda standard library
--
-- Products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product where

open import Function.Base using (_∘_)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Unary using (Pred; _≐_; _∩_; Unique)

private
  variable
    a b c ℓ p q r s : Level
    A B C : Set a


------------------------------------------------------------------------
-- Definition of dependent products

open import Data.Product.Base public

-- These are here as they are not 'basic' but instead "very dependent",
-- i.e. the result type depends on the full input 'point' (x , y).
map-Σ : {B : A → Set b} {P : A → Set p} {Q : {x : A} → P x → B x → Set q} →
   (f : (x : A) → B x) → (∀ {x} → (y : P x) → Q y (f x)) →
   ((x , y) : Σ A P) → Σ (B x) (Q y)
map-Σ f g (x , y) = (f x , g y)

-- This is a "non-dependent" version of map-Σ whereby the input is actually
-- a pair (i.e. _×_ ) but the output type still depends on the input 'point' (x , y).
map-Σ′ : {B : A → Set b} {P : Set p} {Q : P → Set q} →
  (f : (x : A) → B x) → ((x : P) → Q x) → ((x , y) : A × P) → B x × Q y
map-Σ′ f g (x , y) = (f x , g y)

-- This is a generic zipWith for Σ where different functions are applied to each
-- component pair, and recombined.
zipWith : {P : A → Set p} {Q : B → Set q} {R : C → Set r} {S : (x : C) → R x → Set s}
  (_∙_ : A → B → C) → (_∘_ : ∀ {x y} → P x → Q y → R (x ∙ y)) →
  (_*_ : (x : C) → (y : R x) → S x y) →
  ((a , p) : Σ A P) → ((b , q) : Σ B Q) → S (a ∙ b) (p ∘ q)
zipWith _∙_ _∘_ _*_ (a , p) (b , q) = (a ∙ b) * (p ∘ q)

------------------------------------------------------------------------
-- Negation of existential quantifier

∄ : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄ P = ¬ ∃ P

-- Syntax

infix 2 ∄-syntax

∄-syntax : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄-syntax = ∄

syntax ∄-syntax (λ x → B) = ∄[ x ] B

------------------------------------------------------------------------
-- Unique existence (parameterised by an underlying equality).

module _ (_≈_ : Rel A ℓ) where

  ∃! : (P : Pred A p) → Set _
  ∃! P = ∃ (P ∩ Unique _≈_ P)

  ∃!-≐ : {P : Pred A p} {Q : Pred A q} → P ≐ Q → ∃! P → ∃! Q
  ∃!-≐ (P⊆Q , Q⊆P) = map₂ (map P⊆Q (_∘ Q⊆P))
