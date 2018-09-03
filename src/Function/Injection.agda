------------------------------------------------------------------------
-- The Agda standard library
--
-- Injections
------------------------------------------------------------------------

module Function.Injection where

open import Function as Fun using () renaming (_∘_ to _⟨∘⟩_)
open import Level
open import Relation.Binary
open import Function.Equality as F
  using (_⟶_; _⟨$⟩_ ; Π) renaming (_∘_ to _⟪∘⟫_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Injective functions

Injective : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} →
            A ⟶ B → Set _
Injective {A = A} {B} f = ∀ {x y} → f ⟨$⟩ x ≈₂ f ⟨$⟩ y → x ≈₁ y
  where
  open Setoid A renaming (_≈_ to _≈₁_)
  open Setoid B renaming (_≈_ to _≈₂_)

------------------------------------------------------------------------
-- The set of all injections between two setoids

record Injection {f₁ f₂ t₁ t₂}
                 (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                 Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to        : From ⟶ To
    injective : Injective to

  open Π to public

------------------------------------------------------------------------
-- The set of all injections from one set to another (i.e. injections
-- with propositional equality)

infix 3 _↣_

_↣_ : ∀ {f t} → Set f → Set t → Set _
From ↣ To = Injection (P.setoid From) (P.setoid To)

injection : ∀ {f t} {From : Set f} {To : Set t} → (to : From → To) →
            (∀ {x y} → to x ≡ to y → x ≡ y) → From ↣ To
injection to injective = record
  { to        = P.→-to-⟶ to
  ; injective = injective
  }

------------------------------------------------------------------------
-- Identity and composition.

infixr 9 _∘_

id : ∀ {s₁ s₂} {S : Setoid s₁ s₂} → Injection S S
id = record
  { to        = F.id
  ; injective = Fun.id
  }

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂}
        {F : Setoid f₁ f₂} {M : Setoid m₁ m₂} {T : Setoid t₁ t₂} →
      Injection M T → Injection F M → Injection F T
f ∘ g = record
  { to        =          to        f  ⟪∘⟫ to        g
  ; injective = (λ {_} → injective g) ⟨∘⟩ injective f
  } where open Injection
