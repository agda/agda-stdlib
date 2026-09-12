----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with Strong Contraction structural rule + related
-- proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Structural-Rules.W-Logic where

open import Logic.Logic

record W-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_

    strong-contract :
      ∀ {X Y : Struct} {A : Lang} →
      C⟨ ((X ⨾  Y) ⨾ Y) ⟩ ⊢ A →
      -----------------
      C⟨ X ⨾  Y ⟩ ⊢ A

double-if-contract :
  ∀ (Lang : Set) (Struct : Set) (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ : Lang → Lang → Lang) →
  W-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ →
  ∀ {A B C : Lang} →
  ---------------------------
  S (A ⇒ (A ⇒ B)) ⊢ (A ⇒ B)

-- proof from page 28
double-if-contract Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒_ x =
  Logic.if-introduction y
    (Logic.context y
      (W-Logic.strong-contract x)
      (Logic.if-elimination y
        (Logic.if-elimination y
          (Logic.hypothesis y)
          (Logic.hypothesis y))
        (Logic.hypothesis y)))
    where
    y = W-Logic.is-logic x
