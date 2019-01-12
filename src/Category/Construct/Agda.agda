------------------------------------------------------------------------
-- The Agda standard library
--
-- Agda as a category
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Category.Construct.Agda where

open import Level
open import Function
open import Category
open import Category.Structures
open import Relation.Binary using (IsEquivalence; Reflexive; Symmetric; Setoid)
open import Relation.Binary.PropositionalEquality

agdaCat : ∀ ℓ → Category (suc ℓ) ℓ ℓ
agdaCat ℓ = record
  { Obj = Set ℓ
  ; _⇒_ = λ A B → A → B
  ; _≈_ = λ {A} {B} → Setoid._≈_ (A →-setoid B)
  ; id = Function.id
  ; _∘_ = Function._∘′_
  ; isCategory = record
    { assoc = λ x → refl
    ; identityʳ = λ x → refl
    ; identityˡ = λ x → refl
    ; equiv = λ {A} {B} → Setoid.isEquivalence (A →-setoid B)
    ; ∘-respects-≈ = ∘-respects-≈
  } } where
      ∘-respects-≈ : ∀ {A B C}{f h : B → C}{g i : A → B} → f ≗ h → g ≗ i → f ∘ g ≗ h ∘ i
      ∘-respects-≈ {f = f} {i = i} fh gi x = trans (cong f (gi x)) (fh (i x))
