------------------------------------------------------------------------
-- The Agda standard library
--
-- Agda as a category
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Category.Construct.Agda where

open import Category.Category
open import Function
open import Relation.Binary.PropositionalEquality

agdaCat : ∀ ℓ → Category ℓ
agdaCat ℓ = record
  { Obj = Set ℓ
  ; _⇒_ = λ A B → A → B
  ; _≈_ = _≗_
  ; id = Function.id
  ; _∘_ = Function._∘′_
  }
