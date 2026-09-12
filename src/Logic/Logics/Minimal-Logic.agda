----------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition for Minimal Logic (BCWK[⇒, ∧, ∨] in Restall)
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Logics.Minimal-Logic where

open import Logic.Logic
open import Logic.Structural-Rules.B-Logic
open import Logic.Structural-Rules.C-Logic
open import Logic.Structural-Rules.W-Logic
open import Logic.Structural-Rules.K-Logic
open import Logic.Connectives.And-Logic
open import Logic.Connectives.Or-Logic

record Minimal-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ _∧_ _∨_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-and-logic : And-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_ _∧_

    is-or-logic : Or-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_ _∨_

    is-B-logic : B-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-C-logic : C-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-W-logic : W-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-K-logic : K-Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_
