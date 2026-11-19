----------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition for Positive Entailment Logic (DBB'lPrPuW[⇒, ∘, ∧, ∨, t]
-- in Restall)
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Logics.E+-Logic where

open import Logic.Logic
open import Logic.Logics.T+-Logic
open import Logic.Punctuation.Rightid-Logic

record E⁺-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ _/_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ _⇐_ _∧_ _∨_ _∘_ : Lang → Lang → Lang) (t : Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-T⁺-logic :
      T⁺-Logic S _⊢_ C⟨_⟩ _⨾_ _/_ ∅ _⇒_ _⇐_ _∧_ _∨_ _∘_ t

    is-rPu-logic : rPu-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_

