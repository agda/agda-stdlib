------------------------------------------------------------------------
-- The Agda standard library
--
-- Functors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Category
open import Category.Structures

module Category.Functor where

record RawFunctor {oᶜ mᶜ rᶜ}
                  {oᵈ mᵈ rᵈ}
                  (catC : RawCategory oᶜ mᶜ rᶜ)
                  (catD : RawCategory oᵈ mᵈ rᵈ) : Set (oᶜ ⊔ mᶜ ⊔ oᵈ ⊔ mᵈ) where
  private
    module C = RawCategory catC
    module D = RawCategory catD
  field
    F : C.Obj → D.Obj
    fmap : ∀ {A B} → A C.⇒ B → F A D.⇒ F B

RawEndoFunctor : ∀ {o m r} → RawCategory o m r → Set (o ⊔ m)
RawEndoFunctor cat = RawFunctor cat cat

record Functor {oᶜ mᶜ rᶜ}
               {oᵈ mᵈ rᵈ}
               (catC : RawCategory oᶜ mᶜ rᶜ)
               (catD : RawCategory oᵈ mᵈ rᵈ) : Set (oᶜ ⊔ mᶜ ⊔ rᶜ ⊔ oᵈ ⊔ mᵈ ⊔ rᵈ) where
  private
    open Category.Structures.Exo catC catD
    module C = RawCategory catC
    module D = RawCategory catD
  field
    F : C.Obj → D.Obj
    fmap : ∀ {A B} → A C.⇒ B → F A D.⇒ F B
    isFunctor : IsFunctor F fmap

  open IsFunctor isFunctor public

  rawFunctor : RawFunctor catC catD
  rawFunctor = record { fmap = fmap }

EndoFunctor : ∀ {o m r} → RawCategory o m r → Set (o ⊔ m ⊔ r)
EndoFunctor cat = Functor cat cat

-- record RawNaturalTransformation {oᶜ mᶜ rᶜ}
--                                 {oᵈ mᵈ rᵈ}
--                                 (catC : RawCategory oᶜ mᶜ rᶜ)
--                                 (catD : RawCategory oᵈ mᵈ rᵈ)
--                                 (fun₁ fun₂ : RawFunctor catC catD) : Set (oᶜ ⊔ mᵈ) where
--   private
--     module F₁ = RawFunctor fun₁
--     module F₂ = RawFunctor fun₂
--     module D = RawCategory catD
--   field
--     op     : ∀{X} → F₁.F X D.⇒ F₂.F X
