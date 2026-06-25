----------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition for Positive Ticket Entailment (DBB'lP[⇒, ∘, ∧, ∨, t] in
-- Restall)
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Logics.TW+-Logic where

open import Logic.Logic
open import Logic.Logics.Or-Comma-Logic
open import Logic.Structural-Rules.B-Logic
open import Logic.Structural-Rules.B'-Logic
open import Logic.Punctuation.Leftid-Logic
open import Logic.Connectives.Truth-Logic
open import Logic.Connectives.And-Logic
open import Logic.Connectives.Backif-Logic
open import Logic.Connectives.Fusion-Logic

record TW⁺-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ _/_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ _⇐_ _∧_ _∨_ _∘_ : Lang → Lang → Lang) (t : Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-or-comma-logic : Or-Comma-Logic S _⊢_ C⟨_⟩ _⨾_ _/_ _⇒_ _∨_

    is-B-logic : B-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-B'-logic : B'-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-truth-logic : Truth-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_ t

    is-and-logic : And-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_ _∧_

    is-backif-logic : Backif-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_ _⇐_

    is-fusion-logic : Fusion-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_ _∘_

