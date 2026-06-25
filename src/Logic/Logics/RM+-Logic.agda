----------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition for Positive Relevant Logic with Mingle (DBCWM in Restall)
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Logics.RM+-Logic where

open import Logic.Logic
open import Logic.Logics.R+-Logic
open import Logic.Structural-Rules.M-Logic

record RM⁺-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ _/_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ _⇐_ _∧_ _∨_  _∘_ : Lang → Lang → Lang) (t ⊤ ⊥ : Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-R⁺-logic : R⁺-Logic S _⊢_ C⟨_⟩ _⨾_ _/_ ∅ _⇒_ _⇐_ _∧_ _∨_ _∘_ t ⊤ ⊥

    is-M-logic : M-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_

