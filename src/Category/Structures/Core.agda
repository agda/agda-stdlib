------------------------------------------------------------------------
-- The Agda standard library
--
-- Structural definitions over a category
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level renaming (suc to lsuc)
open import Relation.Binary using (IsEquivalence; Setoid; Rel; Reflexive; TransFlip)

module Category.Structures.Core where

record IsCategory {o}{m}{r}
                  (Obj : Set o)
                  (_⇒′_ : Rel Obj m)
                  (_≈′_ : ∀ {A B} → Rel (A ⇒′ B) r)
                  (id  : Reflexive _⇒′_)
                  (_∘′_ : TransFlip _⇒′_ _⇒′_ _⇒′_) : Set (o ⊔ m ⊔ r) where
  private
    infix  4 _≈_ _⇒_
    _≈_ = _≈′_
    _⇒_ = _⇒′_
    infixr 9 _∘_
    _∘_ = _∘′_
  field
    assoc : ∀ {A B C D}{f : A ⇒ B}{g : B ⇒ C}{h : C ⇒ D} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    identityʳ : ∀ {A B}{f : A ⇒ B} → f ∘ id ≈ f
    identityˡ : ∀ {A B}{f : A ⇒ B} → id ∘ f ≈ f
    equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    ∘-respects-≈ : ∀ {A B C}{f h : B ⇒ C}{g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

  ≈-setoid : ∀ A B → Setoid _ _
  ≈-setoid A B = record
    { Carrier = A ⇒ B
    ; _≈_ = _≈_
    ; isEquivalence = equiv
    }

  module ≈-Reasoning {A B : Obj} where
    open Setoid (≈-setoid A B)
      using ()
      renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans) public
    open import Relation.Binary.EqReasoning (≈-setoid A B) public

    infixl 4 _over_ _under_
    _over_ : ∀ {C : Obj}{x y : A ⇒ C} → x ≈ y → (f : C ⇒ B) → f ∘ x ≈ f ∘ y
    eq over f = ∘-respects-≈ (IsEquivalence.refl equiv) eq
    _under_ : ∀ {C : Obj}{x y : B ⇒ C} → x ≈ y → (f : A ⇒ B) → x ∘ f ≈ y ∘ f
    eq under f = ∘-respects-≈ eq (IsEquivalence.refl equiv)
