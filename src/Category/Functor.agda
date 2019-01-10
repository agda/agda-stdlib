------------------------------------------------------------------------
-- The Agda standard library
--
-- Functors
------------------------------------------------------------------------

-- Note that currently the functor laws are not included here.

{-# OPTIONS --without-K --safe #-}

open import Category.Category using (Category)

module Category.Functor {ℓᶜ}{ℓᵈ} (catC : Category ℓᶜ) (catD : Category ℓᵈ) where

open import Level
open Category catC renaming (Obj to ObjC; _⇒_ to _⇒C_; _≈_ to _≈C_; _∘_ to _∘C_)
open Category catD renaming (Obj to ObjD; _⇒_ to _⇒D_; _≈_ to _≈D_; _∘_ to _∘D_)

record RawFunctor (F : ObjC → ObjD) : Set (suc ℓᶜ ⊔ ℓᵈ) where
  field
    fmap : ∀ {A B} → (A ⇒C B) → F A ⇒D F B

record RawMorphism {F₁ F₂ : ObjC → ObjD}
                   (fun₁ : RawFunctor F₁)
                   (fun₂ : RawFunctor F₂) : Set (suc ℓᶜ ⊔ ℓᵈ) where
  open RawFunctor
  field
    op     : ∀{X} → F₁ X ⇒D F₂ X
