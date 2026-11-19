----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with 'right id' connective + related proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Punctuation.Rightid-Logic where

open import Logic.Logic
open import Logic.Connectives.Truth-Logic

record rPu-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_

    right-push :
      ∀ {X : Struct} {A : Lang} →
      C⟨ X ⟩ ⊢ A →
      -----------------
      C⟨ X ⨾ ∅ ⟩ ⊢ A

record rPo-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    right-pop :
      ∀ {X : Struct} {A : Lang} →
      C⟨ X ⨾ ∅ ⟩ ⊢ A →
      ---------------
      C⟨ X ⟩ ⊢ A

record Rightid-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ : Lang → Lang → Lang)  : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-right-push : rPu-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_

    is-right-pop : rPo-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_

t-reduce :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ : Lang → Lang → Lang) (t : Lang) →
  Truth-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_ t →
  rPo-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_ →
  ∀ {A B : Lang} →
  ------------------
  (S (t ⇒ A)) ⊢ A

t-reduce Lang Struct S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_ t x y =
  Logic.context z
    (rPo-Logic.right-pop y)
    (Logic.if-elimination z
      (Logic.hypothesis z)
      (Truth-Logic.t-introduction x))
    where
    z = rPo-Logic.is-logic y
