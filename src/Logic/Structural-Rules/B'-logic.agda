----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with Twisted Associative structural rule + related
-- proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Structural-Rules.B'-Logic where

open import Logic.Logic

record B'-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_

    twisted-assoc :
      ∀ {X Y Z : Struct} {A : Lang} →
      ----------------------------------------------------
      (C⟨ (X ⨾ ( Y ⨾ Z)) ⟩ ⊢ A → C⟨ ((Y ⨾  X) ⨾ Z) ⟩ ⊢ A)
