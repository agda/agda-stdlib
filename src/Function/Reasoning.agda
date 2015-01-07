------------------------------------------------------------------------
-- The Agda standard library
--
-- Combinators to help reasoning about functions.
-- So far these are id, _$_, and _∘_ but with a different notation.
-- This module was suggested after this question StackOverflow:
--   http://stackoverflow.com/questions/22676703/functional-reasoning
------------------------------------------------------------------------

module Function.Reasoning where

open import Level
open import Function

infix 4 _⟧
infixr 3 _─_⟶_
infix 2 _⟦_

_⟧ : ∀ {a} (A : Set a) → A → A
_⟧ _ = id

_⟦_ : ∀ {a b} {A : Set a} (x : A) {B : A → Set b} (f : (x : A) → B x) → B x
x ⟦ f = f x

_─_⟶_ : ∀ {a b c} (A : Set a) {B : A → Set b} (f : (x : A) → B x)
          {C : {x : A} (y : B x) → Set c} (g : ∀ {x} (y : B x) → C y)
          (x : A) → C (f x)
A ─ f ⟶ g = g ∘ f

_─_⟶′_ : ∀ {a b c} (A : Set a) {B : Set b} (f : A → B)
          {C : Set c} (g : B → C) (x : A) → C
A ─ f ⟶′ g = g ∘ f

private
  -- This is an example of the use of these combinators.
  module Example {A B C D : Set} {A→B : A → B} {B→C : B → C} {C→D : C → D} where
    A→D : A → D
    A→D a = a ⟦
     A
      ─ A→B ⟶
     B
      ─ B→C ⟶
     C
      ─ C→D ⟶
     D ⟧
