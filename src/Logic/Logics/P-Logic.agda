----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic containing an id - not included as part of table of
-- logics in the book, but used to define other logics
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Logics.P-Logic where

open import Logic.Logic
open import Logic.Punctuation.Rightid-Logic
open import Logic.Punctuation.Leftid-Logic

record P-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-rightid-logic : Rightid-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_

    is-leftid-logic : Leftid-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_

