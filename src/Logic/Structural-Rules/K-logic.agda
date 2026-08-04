----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with Weakening structural rule + related proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Structural-Rules.K-Logic where

open import Logic.Logic

record K-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    weaken :
      ∀ {X Y : Struct} {A : Lang} →
      (C⟨ X ⟩ ) ⊢ A →
      ------------------
      (C⟨ X ⨾  Y ⟩) ⊢ A

if-weaken :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) →
  K-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ →
  ∀ {A B : Lang} →
  -----------------
  (S A) ⊢ (B ⇒ A)

--proof from page 27
if-weaken Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒_ x =
  Logic.if-introduction y
    (Logic.context y
      (K-Logic.weaken x)
      (Logic.hypothesis y))
    where
    y = K-Logic.is-logic x
