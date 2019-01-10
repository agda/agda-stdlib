------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition of category.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Category.Category where

open import Level using (suc)
open import Relation.Binary using (Reflexive; TransFlip; Rel)

record Category ℓ : Set (suc (suc ℓ)) where
  infix  4 _≈_ _⇒_
  infixr 9 _∘_
  field
    Obj : Set (suc ℓ)
    _⇒_ : Obj → Obj → Set ℓ
    _≈_ : ∀ {A B} → Rel (A ⇒ B) ℓ
    id  : Reflexive _⇒_
    _∘_ : TransFlip _⇒_ _⇒_ _⇒_
