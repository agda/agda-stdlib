----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with backward conditional connective +
-- related proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Connectives.Backif-Logic where

open import Logic.Logic
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

record Backif-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ _⇐_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    backif-introduction :
      ∀ {X : Struct} {A B : Lang} →
      ((S A) ⨾ X) ⊢ B →
      -------------------
      X ⊢ (B ⇐ A)

    backif-elimination :
      ∀ {X Y : Struct} {A B : Lang} →
      X ⊢ (B ⇐ A) →
      Y ⊢ A →
      -------------------
      (Y ⨾ X) ⊢ B


-- Uniqueness of back-conditionals
backif-unique :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ _⇐₁_ _⇐₂_ : Lang → Lang → Lang) →
  Backif-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ _⇐₁_ →
  Backif-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ _⇐₂_ →
  ∀ {A B : Lang} →
  ---------------------------------------------------------
  (S (A ⇐₁ B)) ⊢ (A ⇐₂ B) × (S (A ⇐₂ B)) ⊢ (A ⇐₁ B)

backif-unique Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒_ _⇐₁_ _⇐₂_ x y =
  ⟨ (Backif-Logic.backif-introduction y
      (Backif-Logic.backif-elimination x
        (Logic.hypothesis z)
        (Logic.hypothesis w))) ,
      Backif-Logic.backif-introduction x
        (Backif-Logic.backif-elimination y
          (Logic.hypothesis w)
          (Logic.hypothesis z)) ⟩
    where
    z = Backif-Logic.is-logic x
    w = Backif-Logic.is-logic y
