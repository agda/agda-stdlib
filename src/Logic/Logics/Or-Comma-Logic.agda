----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic containing both 'or' connective and 'comma'
-- punctuation mark. The setup in here is required to allow for correct use of
-- structural rules in a language containing both 'or' and 'comma'
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Logics.Or-Comma-Logic where

open import Logic.Logic
open import Logic.Connectives.Or-Logic
open import Logic.Punctuation.Comma-Logic
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

record Or-Comma-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ _/_ : Struct → Struct → Struct)
  (_⇒_ _∨_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-or-logic : Or-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ _∨_

    is-comma-logic : Comma-Logic S _⊢_ C⟨_⟩ _⨾_ _/_ _⇒_

    comma-product-context-l :
      ∀ {X Y Z W : Struct} {A : Lang} →
      (C⟨ X ⟩ ⊢ A × C⟨ Y ⟩ ⊢ A → C⟨ Z ⟩ ⊢ A) →
      -----------------------------------------------------
      (C⟨ W / X ⟩ ⊢ A × C⟨ W / Y ⟩ ⊢ A → C⟨ W / Z ⟩ ⊢ A)

    comma-product-context-r :
      ∀ {X Y Z W : Struct} {A : Lang} →
      (C⟨ X ⟩ ⊢ A × C⟨ Y ⟩ ⊢ A → C⟨ Z ⟩ ⊢ A) →
      -----------------------------------------------------
      (C⟨ X / W ⟩ ⊢ A × C⟨ Y / W ⟩ ⊢ A → C⟨ Z / W ⟩ ⊢ A)

