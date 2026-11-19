----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with 'left ID' connective + related proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Punctuation.Leftid-Logic where

open import Logic.Logic

record lPu-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    left-push :
      ∀ {X : Struct} {A : Lang} →
      C⟨ X ⟩ ⊢ A →
      -----------------
      C⟨ ∅ ⨾ X ⟩ ⊢ A

record lPo-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    left-pop :
      ∀ {X : Struct} {A : Lang} →
      C⟨ ∅ ⨾  X ⟩ ⊢ A →
      ------------
      C⟨ X ⟩ ⊢ A

record Leftid-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    is-left-push : lPu-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_

    is-left-pop : lPo-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_

--Theorem 2.29 (page 31)
register-consequence-1 :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ : Lang → Lang → Lang) →
  lPu-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_ →
  ∀ {A B : Lang} →
  -------------------------
  (S A) ⊢ B → ∅ ⊢ (A ⇒ B)

register-consequence-1 Lang Struct S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_ x y =
  Logic.if-introduction z (Logic.context z (lPu-Logic.left-push x) y)
    where
    z = lPu-Logic.is-logic x

register-consequence-2 :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct) (∅ : Struct)
  (_⇒_ : Lang → Lang → Lang)  →
  lPo-Logic S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_ → ∀ {A B : Lang} →
  ---------------------------
  ∅ ⊢ (A ⇒ B) → (S A) ⊢ B

register-consequence-2 Lang Struct S _⊢_ C⟨_⟩ _⨾_ ∅ _⇒_ x y =
  Logic.context z
    (lPo-Logic.left-pop x)
    (Logic.if-elimination z y
      (Logic.hypothesis z))
    where
    z = lPo-Logic.is-logic x

