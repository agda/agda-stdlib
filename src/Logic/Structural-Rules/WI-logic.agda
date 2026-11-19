----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with Weak Contraction structural rule
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Structural-Rules.WI-Logic where

open import Logic.Logic

record WI-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    weak-contract :
      ∀ {X : Struct} {A : Lang} →
      C⟨ (X ⨾  X) ⟩ ⊢ A →
      ------------
      C⟨ X ⟩ ⊢ A
