----------------------------------------------------------------------------
-- The Agda standard library
--
-- Logic with 'and' connective + related proof
----------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Logic.Connectives.And-Logic where

open import Logic.Logic

record And-Logic
  {Lang : Set} {Struct : Set} (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct )
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ _∧_ : Lang → Lang → Lang) : Set where
  field
    is-logic : Logic S _⊢_ C⟨_⟩ _⨾_  _⇒_
    and-introduction :
      ∀ {X : Struct} {A B : Lang} →
      X ⊢ A →
      X ⊢ B →
      -------------------
      X ⊢ (A ∧ B)
    and-elimination-1 :
      ∀ {X : Struct} {A B : Lang} →
      X ⊢ (A ∧ B) →
      -------------------
      X ⊢ A
    and-elimination-2 :
      ∀ {X : Struct} {A B : Lang} →
      X ⊢ (A ∧ B) →
      -------------------
      X ⊢ B

if-and-distrib :
  ∀ (Lang : Set) (Struct : Set)
  (S : Lang → Struct)
  (_⊢_ : Struct → Lang → Set)
  (C⟨_⟩ : Struct → Struct)
  (_⨾_ : Struct → Struct → Struct)
  (_⇒_ _∧_ : Lang → Lang → Lang) →
  And-Logic S _⊢_ C⟨_⟩ _⨾_ _⇒_ _∧_ → ∀ {A B C : Lang}  →
  -----------------------------------------------------------------
  (S ((A ⇒ B) ∧ (A ⇒ C))) ⊢ (A ⇒ (B ∧ C))

-- proof from page 34
if-and-distrib Lang Struct S _⊢_ C⟨_⟩ _⨾_ _⇒_ _∧_ x =
  Logic.if-introduction y
    (And-Logic.and-introduction x
      (Logic.if-elimination y
        (And-Logic.and-elimination-1 x
          (Logic.hypothesis y))
        (Logic.hypothesis y))
      (Logic.if-elimination y
        (And-Logic.and-elimination-2 x
          (Logic.hypothesis y))
        (Logic.hypothesis y)))
    where
    y = And-Logic.is-logic x

