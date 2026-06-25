----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with Associative structural rule + related proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Structural-Rules.B-Logic where

open import Logic.Logic

record B-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    assoc :
      ∀ {X Y Z : Struct} {A : Lang} →
      C⟨ (X ⨾ ( Y ⨾ Z)) ⟩ ⊢ A →
      -------------------------
      C⟨ ((X ⨾  Y) ⨾ Z) ⟩ ⊢ A

if-extend :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) →
  B-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ →
  ∀ {A B C : Lang} →
  ------------------------------------
  (S (A ⇒ B)) ⊢ ((C ⇒ A) ⇒ (C ⇒ B))

--proof from page 27
if-extend Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒_ x =
  Logic.if-introduction y
    (Logic.if-introduction y
      (Logic.context y
        (B-Logic.assoc x)
        (Logic.if-elimination y
          (Logic.hypothesis y)
          (Logic.if-elimination y
            (Logic.hypothesis y)
            (Logic.hypothesis y)))))
    where
    y = B-Logic.is-logic x
