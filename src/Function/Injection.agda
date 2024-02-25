------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warn=noUserWarning #-}

module Function.Injection where

{-# WARNING_ON_IMPORT
"Function.Injection was deprecated in v2.0.
Use the standard function hierarchy in Function/Function.Bundles instead."
#-}

open import Function.Base as Fun using () renaming (_∘_ to _⟨∘⟩_)
open import Level
open import Relation.Binary.Bundles using (Setoid)
open import Function.Equality as F
  using (_⟶_; _⟨$⟩_ ; Π) renaming (_∘_ to _⟪∘⟫_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

------------------------------------------------------------------------
-- Injective functions

Injective : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} →
            A ⟶ B → Set _
Injective {A = A} {B} f = ∀ {x y} → f ⟨$⟩ x ≈₂ f ⟨$⟩ y → x ≈₁ y
  where
  open Setoid A renaming (_≈_ to _≈₁_)
  open Setoid B renaming (_≈_ to _≈₂_)
{-# WARNING_ON_USAGE Injective
"Warning: Injective was deprecated in v2.0.
Please use Function.(Definitions.)Injective instead."
#-}

------------------------------------------------------------------------
-- The set of all injections between two setoids

record Injection {f₁ f₂ t₁ t₂}
                 (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                 Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to        : From ⟶ To
    injective : Injective to

  open Π to public
{-# WARNING_ON_USAGE Injection
"Warning: Injection was deprecated in v2.0.
Please use Function.(Bundles.)Injection instead."
#-}

------------------------------------------------------------------------
-- The set of all injections from one set to another (i.e. injections
-- with propositional equality)

infix 3 _↣_

_↣_ : ∀ {f t} → Set f → Set t → Set _
From ↣ To = Injection (≡.setoid From) (≡.setoid To)
{-# WARNING_ON_USAGE _↣_
"Warning: _↣_ was deprecated in v2.0.
Please use Function.(Bundles.)_↣_ instead."
#-}

injection : ∀ {f t} {From : Set f} {To : Set t} → (to : From → To) →
            (∀ {x y} → to x ≡ to y → x ≡ y) → From ↣ To
injection to injective = record
  { to        = record
    { _⟨$⟩_ = to
    ; cong = ≡.cong to
    }
  ; injective = injective
  }
{-# WARNING_ON_USAGE injection
"Warning: injection was deprecated in v2.0.
Please use Function.(Bundles.)mk↣ instead."
#-}

------------------------------------------------------------------------
-- Identity and composition.

infixr 9 _∘_

id : ∀ {s₁ s₂} {S : Setoid s₁ s₂} → Injection S S
id = record
  { to        = F.id
  ; injective = Fun.id
  }
{-# WARNING_ON_USAGE id
"Warning: id was deprecated in v2.0.
Please use Function.Properties.Injection.refl or
Function.Construct.Identity.injection instead."
#-}

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂}
        {F : Setoid f₁ f₂} {M : Setoid m₁ m₂} {T : Setoid t₁ t₂} →
      Injection M T → Injection F M → Injection F T
f ∘ g = record
  { to        =          to        f  ⟪∘⟫ to        g
  ; injective = (λ {_} → injective g) ⟨∘⟩ injective f
  } where open Injection
{-# WARNING_ON_USAGE _∘_
"Warning: _∘_ was deprecated in v2.0.
Please use Function.Properties.Injection.trans or
Function.Construct.Composition.injection instead."
#-}
