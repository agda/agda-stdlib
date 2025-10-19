----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with 'fusion' connective + related proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Connectives.Fusion-Logic where

open import Logic.Logic
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

record Fusion-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ _∘_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_

    fusion-introduction :
      ∀ {X Y : Struct} {A B : Lang} →
      X ⊢ A → Y ⊢ B →
      -------------------
      (X ⨾ Y) ⊢ (A ∘ B)

    fusion-elimination :
      ∀ {X : Struct} {A B C : Lang} →
      X ⊢ (A ∘ B) →
      ------------------------------------------
      C⟨ (S A) ⨾ (S B) ⟩ ⊢ C → C⟨ X ⟩ ⊢ C


-- Lemma 2.25 (Uniqueness of fusion)
fusion-unique :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ _∘₁_ _∘₂_ : Lang → Lang → Lang) →
  Fusion-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ _∘₁_ →
  Fusion-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ _∘₂_  →
  ∀ {A B : Lang} →
  ---------------------------------------------------------
  (S (A ∘₁ B)) ⊢ (A ∘₂ B) × (S (A ∘₂ B)) ⊢ (A ∘₁ B)

fusion-unique Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒_ _∘₁_ _∘₂_ x y =
  ⟨ Logic.context z
      (Fusion-Logic.fusion-elimination x (Logic.hypothesis w))
      (Fusion-Logic.fusion-introduction y
          (Logic.hypothesis w)
          (Logic.hypothesis w)) ,
    Logic.context w
      (Fusion-Logic.fusion-elimination y (Logic.hypothesis z))
      (Fusion-Logic.fusion-introduction x
          (Logic.hypothesis z)
          (Logic.hypothesis z)) ⟩
    where
    z = Fusion-Logic.is-logic x
    w = Fusion-Logic.is-logic y
