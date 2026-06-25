----------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition for Positive Ticket Entailment (DBB'lPW[⇒, ∘, ∧, ∨, t] in
-- Restall)
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Logics.T+-Logic where

open import Logic.Logic
open import Logic.Logics.TW+-Logic
open import Logic.Structural-Rules.W-Logic

record T⁺-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ _/_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ _⇐_ _∧_ _∨_ _∘_ : Lang → Lang → Lang) (t : Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-TW⁺-logic : TW⁺-Logic S _⊢_ C⟨_⟩ _⨾_ _/_ ∅ _⇒_ _⇐_ _∧_ _∨_ _∘_ t

    is-W-logic : W-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_

