----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with Strong Commutatitivity structural rule +
-- related proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Structural-Rules.C-Logic where

open import Logic.Logic

record C-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_

    strong-commute : ∀ {X Y Z : Struct} {A : Lang} →
      C⟨ ((X ⨾  Y) ⨾ Z) ⟩ ⊢ A →
      -----------------------------
      C⟨ ((X ⨾  Z) ⨾ Y) ⟩ ⊢ A

if-rearrange :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) →
  C-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ →
  ∀ {A B C : Lang} →
  -----------------------------------
  (S (A ⇒ (B ⇒ C))) ⊢ (B ⇒ (A ⇒ C))

--proof from page 27
if-rearrange Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒_ x =
  Logic.if-introduction y
    (Logic.if-introduction y
      ( Logic.context y
        (C-Logic.strong-commute x)
        (Logic.if-elimination y
          (Logic.if-elimination y
            (Logic.hypothesis y)
            (Logic.hypothesis y))
          (Logic.hypothesis y))))
    where
    y = C-Logic.is-logic x
