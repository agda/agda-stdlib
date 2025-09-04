----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic containing all connectives - not defined directly in
-- the book but used for easily defining other logics
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Logics.Full-Conn-Logic where

open import Logic.Logic
open import Logic.Connectives.And-Logic
open import Logic.Connectives.Or-Logic
open import Logic.Connectives.Backif-Logic
open import Logic.Connectives.Fusion-Logic
open import Logic.Connectives.Trivial-Logic
open import Logic.Connectives.Truth-Logic

record Full-Conn-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ _⇐_ _∧_ _∨_ _∘_ : Lang → Lang → Lang) (t ⊤ ⊥ : Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-and-logic : And-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_ _∧_

    is-or-logic : Or-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_ _∨_

    is-fusion-logic : Fusion-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_ _∘_

    is-backif-logic : Backif-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_ _⇐_

    is-trivial-logic : Trivial-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_ ⊤ ⊥

    is-truth-logic : Truth-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_ t

