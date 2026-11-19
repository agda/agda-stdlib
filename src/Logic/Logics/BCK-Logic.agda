----------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition for Positive Affine Logic (BCK in Restall)
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Logics.BCK-Logic where

open import Logic.Logic
open import Logic.Logics.MALL+-Logic
open import Logic.Structural-Rules.K-Logic

record BCK-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ _⇐_ _∧_ _∨_  _∘_ : Lang → Lang → Lang) (t ⊤ ⊥ : Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-MALL⁺-logic :
      MALL⁺-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_ _⇐_ _∧_ _∨_ _∘_ t ⊤ ⊥

    is-K-logic : K-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

