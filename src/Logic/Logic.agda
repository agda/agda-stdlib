------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic + some basic proofs about conditional
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Logic where

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

record Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang)  : Set where
  field
    hypothesis :
      ∀ {A : Lang} →
      -------------------
      (S A) ⊢ A

    context :
      ∀ {X X' : Struct} {A : Lang} →
      (C⟨ X ⟩ ⊢ A → C⟨ X' ⟩ ⊢ A) →
      X ⊢ A →
      ---------
      X' ⊢ A

    semicolon--context-l :
      ∀ {X X' Y Y' Z : Struct} {A : Lang} →
      (C⟨ X ⟩ ⊢ A → C⟨ X' ⟩ ⊢ A) →
      ----------------------------------------
      (C⟨ Y ⨾ X ⟩ ⊢ A → C⟨ Y ⨾ X' ⟩ ⊢ A)

    semicolon--context-r :
      ∀ {X X' Y : Struct} {A : Lang} →
      (C⟨ X ⟩ ⊢ A → C⟨ X' ⟩ ⊢ A) →
      ----------------------------------------
      (C⟨ X ⨾ Y ⟩ ⊢ A → C⟨ X' ⨾ Y ⟩ ⊢ A)

    if-introduction :
      ∀ {X : Struct} {A B : Lang} →
      (X ⨾ (S A)) ⊢ B →
      -------------
      X ⊢ (A ⇒ B)

    if-elimination :
      ∀ {X Y : Struct} {A B : Lang} →
      X ⊢ (A ⇒ B) →
      Y ⊢ A →
      -------------
      (X ⨾ Y) ⊢ B

-- proof from page 23
chain-ifs :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) →
  Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ →
  ∀ {A B C : Lang} →
  (S A) ⊢ B →
  ------------------------
  (S (B ⇒ C)) ⊢ (A ⇒ C)


chain-ifs Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒_ x y =  Logic.if-introduction x(Logic.if-elimination x (Logic.hypothesis x) y)

-- Lemma 2.22 (Uniqueness of conditionals)
conditional-unique :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒₁_ _⇒₂_ : Lang → Lang → Lang) →
  Logic S _⊢_ C⟨_⟩ _⨾_ _⇒₁_ →
  Logic S _⊢_ C⟨_⟩ _⨾_ _⇒₂_ →
  ∀ {A B : Lang} →
  ------------------------------------------------
  S (A ⇒₁ B) ⊢ (A ⇒₂ B) × S (A ⇒₂ B) ⊢ (A ⇒₁ B)

conditional-unique Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒₁_ _⇒₂_ x y =
  ⟨ Logic.if-introduction y
      (Logic.if-elimination x
        (Logic.hypothesis x)
        (Logic.hypothesis x)) ,
    Logic.if-introduction x
      (Logic.if-elimination y
        (Logic.hypothesis x)
        (Logic.hypothesis x)) ⟩
