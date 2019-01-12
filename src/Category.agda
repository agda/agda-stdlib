------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition of category.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Category where

open import Level using (suc; Level; _⊔_)
open import Relation.Binary using (Reflexive; TransFlip; Rel)
open import Category.Structures.Core

record RawCategory o m r : Set (suc (o ⊔ m ⊔ r)) where
  infix  4 _≈_ _⇒_
  infixr 9 _∘_
  field
    Obj : Set o
    _⇒_ : Rel Obj m
    _≈_ : ∀ {A B} → Rel (A ⇒ B) r
    id  : Reflexive _⇒_
    _∘_ : TransFlip _⇒_ _⇒_ _⇒_

record Category o m r : Set (suc (o ⊔ m ⊔ r)) where
  infix  4 _≈_ _⇒_
  infixr 9 _∘_
  field
    Obj : Set o
    _⇒_ : Rel Obj m
    _≈_ : ∀ {A B} → Rel (A ⇒ B) r
    id  : Reflexive _⇒_
    _∘_ : TransFlip _⇒_ _⇒_ _⇒_
    isCategory : IsCategory Obj _⇒_ _≈_ id _∘_

  open IsCategory isCategory public

  rawCategory : RawCategory _ _ _
  rawCategory = record { Obj = Obj ; _⇒_ = _⇒_ ; _≈_ = _≈_ ; id = id ; _∘_ = _∘_ }
