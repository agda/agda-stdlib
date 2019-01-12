------------------------------------------------------------------------
-- The Agda standard library
--
-- Structural definitions over a category
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level renaming (suc to lsuc)
open import Relation.Binary using (IsEquivalence; Setoid; Rel; Reflexive; TransFlip)
open import Category

module Category.Structures where

module Exo {oᶜ mᶜ rᶜ}
           {oᵈ mᵈ rᵈ}
           (catC : RawCategory oᶜ mᶜ rᶜ)
           (catD : RawCategory oᵈ mᵈ rᵈ) where
  private
    module C = RawCategory catC
    module D = RawCategory catD

  record IsFunctor (F : C.Obj → D.Obj)
                   (fmap : ∀ {A B} → A C.⇒ B → F A D.⇒ F B) : Set (oᶜ ⊔ mᶜ ⊔ rᶜ ⊔ rᵈ) where
    field
      fmap-identity     : ∀ {A} → fmap (C.id {x = A}) D.≈ D.id
      fmap-homomorphism : ∀ {A B C}{f : B C.⇒ C}{g : A C.⇒ B}
                        → fmap (f C.∘ g) D.≈ fmap f D.∘ fmap g
      fmap-respects-≗   : ∀ {A B}{f : A C.⇒ B}{g : A C.⇒ B}
                        → f C.≈ g
                        → fmap f D.≈ fmap g


--   record IsNatural {F₁ F₂ : Obj → ObjD}
--                    {fun₁ : RawFunctor F₁}
--                    {fun₂ : RawFunctor F₂}
--                    (morph : RawMorphism fun₁ fun₂) : Set (lsuc ℓ ⊔ ℓᵈ) where
--     open RawFunctor
--     open RawMorphism morph
--     field
--       op-<$> : ∀{X Y} (f : X ⇒ Y) → op ∘D (fmap fun₁ f) ≈D (fmap fun₂ f) ∘D op

module Endo {o m r}
            (cat : RawCategory o m r) where
  open Exo cat cat public
  open RawCategory cat

  record IsInitial (⊥ : Obj)
                   (! : ∀ A → ⊥ ⇒ A) : Set (o ⊔ m ⊔ r) where
    field
      !-unique : ∀ {A} → (f : ⊥ ⇒ A) → ! A ≈ f

  record IsTerminal (⊤ : Obj)
                    (! : ∀ A → A ⇒ ⊤) : Set (o ⊔ m ⊔ r) where
    field
      !-unique : ∀ {A} → (f : A ⇒ ⊤) → ! A ≈ f
