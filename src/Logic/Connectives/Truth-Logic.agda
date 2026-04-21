----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with 'truth' connective + related proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Connectives.Truth-Logic where

open import Logic.Punctuation.Leftid-Logic
open import Logic.Logic
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)


record Truth-Logic {Lang : Set} {Struct : Set} (S : Lang → Struct) (_⊢_ : Struct → Lang → Set) (C⟨_⟩ : Struct → Struct ) (_⨾_ : Struct → Struct → Struct) (∅ : Struct) (_⇒_ : Lang → Lang → Lang) (t : Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-leftid-Logic : Leftid-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_

    t-introduction : ∅ ⊢ t

    t-elimination :
      ∀ {X : Struct} {A : Lang} →
      X ⊢ t → C⟨ ∅ ⟩ ⊢ A →
      ------------
      C⟨ X ⟩ ⊢ A

-- Exercise 2.13 (Uniqueness of truth constant)
unique-truth :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ : Lang → Lang → Lang)  (t₁ t₂ : Lang) →
  Truth-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_  t₁ →
  Truth-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_ t₂ →
  -----------------------------
  (S t₁) ⊢ t₂ × (S t₂) ⊢ t₁

unique-truth Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒_ ∅ t₁ t₂ x y =
  ⟨ Logic.context n
      (Truth-Logic.t-elimination x
        (Logic.hypothesis m))
      (Truth-Logic.t-introduction y) ,
    Logic.context m
      (Truth-Logic.t-elimination y
        (Logic.hypothesis n))
      (Truth-Logic.t-introduction x) ⟩
    where
    z = Truth-Logic.is-leftid-Logic x
    w = Truth-Logic.is-leftid-Logic y
    m = Leftid-Logic.is-logic z
    n = Leftid-Logic.is-logic w
