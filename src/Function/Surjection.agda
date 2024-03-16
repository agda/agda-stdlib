------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warn=noUserWarning #-}

module Function.Surjection where

{-# WARNING_ON_IMPORT
"Function.Surjection was deprecated in v2.0.
Use the standard function hierarchy in Function/Function.Bundles instead."
#-}

open import Level
open import Function.Equality as F
  using (_⟶_) renaming (_∘_ to _⟪∘⟫_)
open import Function.Equivalence using (Equivalence)
open import Function.Injection           hiding (id; _∘_; injection)
open import Function.LeftInverse as Left hiding (id; _∘_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

------------------------------------------------------------------------
-- Surjective functions.

record Surjective {f₁ f₂ t₁ t₂}
                  {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
                  (to : From ⟶ To) :
                  Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    from             : To ⟶ From
    right-inverse-of : from RightInverseOf to
{-# WARNING_ON_USAGE Surjective
"Warning: Surjective was deprecated in v2.0.
Please use Function.(Definitions.)Surjective instead."
#-}

------------------------------------------------------------------------
-- The set of all surjections from one setoid to another.

record Surjection {f₁ f₂ t₁ t₂}
                  (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                  Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to         : From ⟶ To
    surjective : Surjective to

  open Surjective surjective public

  right-inverse : RightInverse From To
  right-inverse = record
    { to              = from
    ; from            = to
    ; left-inverse-of = right-inverse-of
    }

  open LeftInverse right-inverse public
    using () renaming (to-from to from-to)

  injective : Injective from
  injective = LeftInverse.injective right-inverse

  injection : Injection To From
  injection = LeftInverse.injection right-inverse

  equivalence : Equivalence From To
  equivalence = record
    { to   = to
    ; from = from
    }
{-# WARNING_ON_USAGE Surjection
"Warning: Surjection was deprecated in v2.0.
Please use Function.(Bundles.)Surjection instead."
#-}

-- Right inverses can be turned into surjections.

fromRightInverse :
  ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
  RightInverse From To → Surjection From To
fromRightInverse r = record
  { to         = from
  ; surjective = record
    { from             = to
    ; right-inverse-of = left-inverse-of
    }
  } where open LeftInverse r
{-# WARNING_ON_USAGE fromRightInverse
"Warning: fromRightInverse was deprecated in v2.0.
Please use Function.(Properties.)RightInverse.RightInverse⇒Surjection instead."
#-}

------------------------------------------------------------------------
-- The set of all surjections from one set to another (i.e. sujections
-- with propositional equality)

infix 3 _↠_

_↠_ : ∀ {f t} → Set f → Set t → Set _
From ↠ To = Surjection (≡.setoid From) (≡.setoid To)
{-# WARNING_ON_USAGE _↠_
"Warning: _↠_ was deprecated in v2.0.
Please use Function.(Bundles.)_↠_ instead."
#-}

surjection : ∀ {f t} {From : Set f} {To : Set t} →
             (to : From → To) (from : To → From) →
             (∀ x → to (from x) ≡ x) →
             From ↠ To
surjection to from surjective = record
  { to         = F.→-to-⟶ to
  ; surjective = record
    { from             = F.→-to-⟶ from
    ; right-inverse-of = surjective
    }
  }
{-# WARNING_ON_USAGE surjection
"Warning: surjection was deprecated in v2.0.
Please use Function.(Bundles.)mk↠ instead."
#-}

------------------------------------------------------------------------
-- Identity and composition.

id : ∀ {s₁ s₂} {S : Setoid s₁ s₂} → Surjection S S
id {S = S} = record
  { to         = F.id
  ; surjective = record
    { from             = LeftInverse.to              id′
    ; right-inverse-of = LeftInverse.left-inverse-of id′
    }
  } where id′ = Left.id {S = S}
{-# WARNING_ON_USAGE id
"Warning: id was deprecated in v2.0.
Please use Function.Properties.Surjection.refl or
Function.Construct.Identity.surjection instead."
#-}

infixr 9 _∘_

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂}
        {F : Setoid f₁ f₂} {M : Setoid m₁ m₂} {T : Setoid t₁ t₂} →
      Surjection M T → Surjection F M → Surjection F T
f ∘ g = record
  { to         = to f ⟪∘⟫ to g
  ; surjective = record
    { from             = LeftInverse.to              g∘f
    ; right-inverse-of = LeftInverse.left-inverse-of g∘f
    }
  }
  where
  open Surjection
  g∘f = Left._∘_ (right-inverse g) (right-inverse f)
{-# WARNING_ON_USAGE _∘_
"Warning: _∘_ was deprecated in v2.0.
Please use Function.Properties.Surjection.trans or
Function.Construct.Composition.surjection instead."
#-}
