----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with Weak Commutatitivity structural rule + related
-- proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Structural-Rules.CI-Logic where

open import Logic.Logic

record CI-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_

    weak-commute :
      ∀ {X Y : Struct} {A : Lang} →
      C⟨ X ⨾ Y ⟩ ⊢ A →
      -----------------
      C⟨ Y ⨾ X ⟩ ⊢ A


modus-ponens-pullback :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) → CI-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ → ∀ {A B : Lang} →
  -----------------------
  (S A) ⊢ ((A ⇒ B) ⇒ B)


-- proof from page 27
modus-ponens-pullback Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒_ x =
  Logic.if-introduction y
    (Logic.context y
      (CI-Logic.weak-commute x)
      (Logic.if-elimination y
        (Logic.hypothesis y)
        (Logic.hypothesis y)))
  where
  y = CI-Logic.is-logic x
