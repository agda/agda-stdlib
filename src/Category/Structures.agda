------------------------------------------------------------------------
-- The Agda standard library
--
-- Structural definitions over a category
------------------------------------------------------------------------

open import Level renaming (suc to lsuc)
open import Relation.Binary using (IsEquivalence; Setoid; Rel)
open import Category.Category
  using (Category)

module Category.Structures {ℓ} (cat : Category ℓ) where

open Category cat

record IsCategory : Set (lsuc ℓ) where
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

-- constructions involving a second, target category
module _ {ℓᵈ} (catD : Category ℓᵈ) where
  open import Category.Functor cat catD
    using (RawFunctor; RawMorphism)
  open Category catD renaming (Obj to ObjD; id to idD; _∘_ to _∘D_; _≈_ to _≈D_; _⇒_ to _⇒D_)

  record IsFunctor {F : Obj → ObjD} (fun : RawFunctor F) : Set (lsuc ℓ ⊔ ℓᵈ) where
    open RawFunctor fun
    field
      fmap-identity     : ∀ {A : Obj} → fmap (id {x = A}) ≈D idD
      fmap-homomorphism : ∀ {A B C : Obj}{f : B ⇒ C}{g : A ⇒ B}
                         → fmap (f ∘ g) ≈D fmap f ∘D fmap g
      fmap-respects-≗   : ∀ {A B}{f : A ⇒ B}{g : A ⇒ B}
                       → f ≈ g
                       → fmap f ≈D fmap g

  record IsNatural {F₁ F₂ : Obj → ObjD}
                   {fun₁ : RawFunctor F₁}
                   {fun₂ : RawFunctor F₂}
                   (morph : RawMorphism fun₁ fun₂) : Set (lsuc ℓ ⊔ ℓᵈ) where
    open RawFunctor
    open RawMorphism morph
    field
      op-<$> : ∀{X Y} (f : X ⇒ Y) → op ∘D (fmap fun₁ f) ≈D (fmap fun₂ f) ∘D op

-- constructions in a single category
open import Category.InitialObject cat

record IsInitial (ini : RawInitial) : Set (lsuc ℓ) where
  open RawInitial ini
  field
    uniqueUniversality : ∀ {X} (morph : Universal ⇒ X) → universality X ≈ morph
