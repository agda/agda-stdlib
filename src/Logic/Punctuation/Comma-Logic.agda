----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with 'comma' punctuation
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Punctuation.Comma-Logic where

open import Logic.Logic

record Comma-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ _/_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_

    comma-assoc :
      ∀ {X Y Z : Struct} {A : Lang} →
      C⟨ X  / (Y / Z) ⟩  ⊢ A →
      -----------------------------
      C⟨ (X /  Y) / Z ⟩ ⊢ A

    comma-commute :
      ∀ {X Y : Struct} {A : Lang} →
      C⟨ X  / Y ⟩ ⊢ A →
      -----------------------------
      C⟨ Y /  X ⟩ ⊢ A

    comma-contract :
      ∀ {X : Struct} {A : Lang} →
      C⟨ X / X ⟩  ⊢ A →
      ---------------
      C⟨ X ⟩ ⊢ A

    comma-weaken :
      ∀ {X Y : Struct} {A : Lang} →
      C⟨ X ⟩ ⊢ A →
      -------------------
      C⟨ X / Y ⟩ ⊢ A

    comma-context-l :
      ∀ {X X' Y : Struct} {A : Lang} →
      (C⟨ X ⟩ ⊢ A → C⟨ X' ⟩ ⊢ A) →
      -----------------------------------------
      (C⟨ (Y / X) ⟩ ⊢ A → C⟨ (Y / X') ⟩ ⊢ A)

    comma-context-r :
      ∀ {X X' Y : Struct} {A : Lang} →
      (C⟨ X ⟩ ⊢ A → C⟨ X' ⟩ ⊢ A) →
      -----------------------------------------
      (C⟨ (X / Y) ⟩ ⊢ A → C⟨ (X' / Y) ⟩ ⊢ A)
