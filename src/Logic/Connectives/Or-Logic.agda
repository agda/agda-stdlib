----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with 'or' connective + related proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Connectives.Or-Logic where

open import Logic.Logic
open import Logic.Connectives.And-Logic
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

record Or-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ _∨_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    product-context :
      ∀ {X Y Z : Struct} {A : Lang} →
      (C⟨ X ⟩ ⊢ A × C⟨ Y ⟩ ⊢ A → C⟨ Z ⟩ ⊢ A) →
      X ⊢ A × Y ⊢ A  →
      ---------
      Z ⊢ A

    semicolon-product-context-l :
      ∀ {X Y Z W : Struct} {A : Lang} →
      (C⟨ X ⟩ ⊢ A × C⟨ Y ⟩ ⊢ A → C⟨ Z ⟩ ⊢ A) →
      ----------------------------------------
      (C⟨ W ⨾ X ⟩ ⊢ A × C⟨ W ⨾ Y ⟩ ⊢ A → C⟨ W ⨾ Z ⟩ ⊢ A)

    semicolon-product-context-r :
      ∀ {X Y Z W : Struct} {A : Lang} →
      (C⟨ X ⟩ ⊢ A × C⟨ Y ⟩ ⊢ A → C⟨ Z ⟩ ⊢ A) →
      ----------------------------------------
      (C⟨ X ⨾ W ⟩ ⊢ A × C⟨ Y ⨾ W ⟩ ⊢ A → C⟨ Z ⨾ W ⟩ ⊢ A)

    or-introduction-1 :
      ∀ {X : Struct} {A B : Lang} →
      X ⊢ A →
      ---------
      X ⊢ (A ∨ B)

    or-introduction-2 :
      ∀ {X : Struct} {A B : Lang} →
      X ⊢ B →
      ---------------
      X ⊢ (A ∨ B)

    or-elimination :
      ∀ {X : Struct} {A B C : Lang} →
      X ⊢ (A ∨ B) →
      --------------------------------------------------
      (C⟨ (S A) ⟩ ⊢ C × C⟨ (S B) ⟩ ⊢ C  → C⟨ X ⟩ ⊢ C)


or-if-distrib :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ _∧_ _∨_ : Lang → Lang → Lang) →
  Or-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ _∨_ →
  And-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ _∧_ →
  ∀ {A B C : Lang} →
  ---------------------------------------
  S ((A ⇒ C) ∧ (B ⇒ C)) ⊢ ((A ∨ B) ⇒ C)

or-if-distrib Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒_ _∧_ _∨_ x y =
   Logic.if-introduction z
    (Or-Logic.product-context x
      (Or-Logic.semicolon-product-context-l x
        (Or-Logic.or-elimination x
          (Logic.hypothesis z)))
      ⟨ Logic.if-elimination z
        (And-Logic.and-elimination-1 y
          (Logic.hypothesis z))
        (Logic.hypothesis z) ,
        Logic.if-elimination z
          (And-Logic.and-elimination-2 y
            (Logic.hypothesis z))
          (Logic.hypothesis z) ⟩)
    where
    z = Or-Logic.is-logic x
