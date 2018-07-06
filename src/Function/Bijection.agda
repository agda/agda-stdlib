------------------------------------------------------------------------
-- The Agda standard library
--
-- Bijections
------------------------------------------------------------------------

module Function.Bijection where

open import Data.Product
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open import Function.Equality as F
  using (_⟶_; _⟨$⟩_) renaming (_∘_ to _⟪∘⟫_)
open import Function.Injection   as Inj  hiding (id; _∘_; injection)
open import Function.Surjection  as Surj hiding (id; _∘_; surjection)
open import Function.LeftInverse as Left hiding (id; _∘_; leftInverse)

------------------------------------------------------------------------
-- Bijective functions.

record Bijective {f₁ f₂ t₁ t₂}
                 {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
                 (to : From ⟶ To) :
                 Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    injective  : Injective  to
    surjective : Surjective to

  open Surjective surjective public

  left-inverse-of : from LeftInverseOf to
  left-inverse-of x = injective (right-inverse-of (to ⟨$⟩ x))

------------------------------------------------------------------------
-- The set of all bijections between two setoids.

record Bijection {f₁ f₂ t₁ t₂}
                 (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                 Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to        : From ⟶ To
    bijective : Bijective to

  open Bijective bijective public

  injection : Injection From To
  injection = record
    { to        = to
    ; injective = injective
    }

  surjection : Surjection From To
  surjection = record
    { to         = to
    ; surjective = surjective
    }

  open Surjection surjection public
    using (equivalence; right-inverse; from-to)

  left-inverse : LeftInverse From To
  left-inverse = record
    { to              = to
    ; from            = from
    ; left-inverse-of = left-inverse-of
    }

  open LeftInverse left-inverse public using (to-from)

------------------------------------------------------------------------
-- The set of all bijections between two sets (i.e. bijections with
-- propositional equality)

infix 3 _⤖_

_⤖_ : ∀ {f t} → Set f → Set t → Set _
From ⤖ To = Bijection (P.setoid From) (P.setoid To)

bijection : ∀ {f t} {From : Set f} {To : Set t} →
            (to : From → To) (from : To → From) →
            (∀ {x y} → to x ≡ to y → x ≡ y) →
            (∀ x → to (from x) ≡ x) →
            From ⤖ To
bijection to from inj invʳ = record
  { to        = P.→-to-⟶ to
  ; bijective = record
    { injective  = inj
    ; surjective = record
      { from             = P.→-to-⟶ from
      ; right-inverse-of = invʳ
      }
    }
  }

------------------------------------------------------------------------
-- Identity and composition. (Note that these proofs are superfluous,
-- given that Bijection is equivalent to Function.Inverse.Inverse.)

id : ∀ {s₁ s₂} {S : Setoid s₁ s₂} → Bijection S S
id {S = S} = record
  { to        = F.id
  ; bijective = record
    { injective  =  Injection.injective   (Inj.id {S = S})
    ; surjective = Surjection.surjective (Surj.id {S = S})
    }
  }

infixr 9 _∘_

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂}
        {F : Setoid f₁ f₂} {M : Setoid m₁ m₂} {T : Setoid t₁ t₂} →
      Bijection M T → Bijection F M → Bijection F T
f ∘ g = record
  { to        = to f ⟪∘⟫ to g
  ; bijective = record
    { injective  =  Injection.injective   (Inj._∘_  (injection f)  (injection g))
    ; surjective = Surjection.surjective (Surj._∘_ (surjection f) (surjection g))
    }
  } where open Bijection
