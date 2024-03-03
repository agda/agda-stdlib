------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warn=noUserWarning #-}

module Function.LeftInverse where

{-# WARNING_ON_IMPORT
"Function.LeftInverse was deprecated in v2.0.
Use the standard function hierarchy in Function/Function.Bundles instead."
#-}

open import Level
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Binary.Bundles using (Setoid)
open import Function.Equality as Eq
  using (_⟶_; _⟨$⟩_) renaming (_∘_ to _⟪∘⟫_)
open import Function.Equivalence using (Equivalence)
open import Function.Injection using (Injective; Injection)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

------------------------------------------------------------------------
-- Left and right inverses.

_LeftInverseOf_ :
  ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
  To ⟶ From → From ⟶ To → Set _
_LeftInverseOf_ {From = From} f g = ∀ x → f ⟨$⟩ (g ⟨$⟩ x) ≈ x
  where open Setoid From
{-# WARNING_ON_USAGE _LeftInverseOf_
"Warning: _LeftInverseOf_ was deprecated in v2.0.
Please use Function.(Structures.)IsRightInverse instead."
#-}

_RightInverseOf_ :
  ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
  To ⟶ From → From ⟶ To → Set _
f RightInverseOf g = g LeftInverseOf f
{-# WARNING_ON_USAGE _RightInverseOf_
"Warning: _RightInverseOf_ was deprecated in v2.0.
Please use Function.(Structures.)IsLeftInverse instead."
#-}

------------------------------------------------------------------------
-- The set of all left inverses between two setoids.

record LeftInverse {f₁ f₂ t₁ t₂}
                   (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                   Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to              : From ⟶ To
    from            : To ⟶ From
    left-inverse-of : from LeftInverseOf to

  private
    open module F = Setoid From
    open module T = Setoid To
  open EqReasoning From

  injective : Injective to
  injective {x} {y} eq = begin
    x                    ≈⟨ F.sym (left-inverse-of x) ⟩
    from ⟨$⟩ (to ⟨$⟩ x)  ≈⟨ Eq.cong from eq ⟩
    from ⟨$⟩ (to ⟨$⟩ y)  ≈⟨ left-inverse-of y ⟩
    y                    ∎

  injection : Injection From To
  injection = record { to = to; injective = injective }

  equivalence : Equivalence From To
  equivalence = record
    { to   = to
    ; from = from
    }

  to-from : ∀ {x y} → to ⟨$⟩ x T.≈ y → from ⟨$⟩ y F.≈ x
  to-from {x} {y} to-x≈y = begin
    from ⟨$⟩ y           ≈⟨ Eq.cong from (T.sym to-x≈y) ⟩
    from ⟨$⟩ (to ⟨$⟩ x)  ≈⟨ left-inverse-of x ⟩
    x                    ∎
{-# WARNING_ON_USAGE LeftInverse
"Warning: LeftInverse was deprecated in v2.0.
Please use Function.(Bundles.)RightInverse instead."
#-}

-- The set of all right inverses between two setoids.

RightInverse : ∀ {f₁ f₂ t₁ t₂}
               (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) → Set _
RightInverse From To = LeftInverse To From
{-# WARNING_ON_USAGE RightInverse
"Warning: RightInverse was deprecated in v2.0.
Please use Function.(Bundles.)LeftInverse instead."
#-}

------------------------------------------------------------------------
-- The set of all left inverses from one set to another (i.e. left
-- inverses with propositional equality).
--
-- Read A ↞ B as "surjection from B to A".

infix 3 _↞_

_↞_ : ∀ {f t} → Set f → Set t → Set _
From ↞ To = LeftInverse (≡.setoid From) (≡.setoid To)
{-# WARNING_ON_USAGE _↞_
"Warning: _↞_ was deprecated in v2.0.
Please use Function.(Bundles.)_↪_ instead."
#-}

leftInverse : ∀ {f t} {From : Set f} {To : Set t} →
              (to : From → To) (from : To → From) →
              (∀ x → from (to x) ≡ x) →
              From ↞ To
leftInverse to from invˡ = record
  { to              = Eq.→-to-⟶ to
  ; from            = Eq.→-to-⟶ from
  ; left-inverse-of = invˡ
  }
{-# WARNING_ON_USAGE leftInverse
"Warning: leftInverse was deprecated in v2.0.
Please use Function.(Bundles.)mk↪ instead."
#-}

------------------------------------------------------------------------
-- Identity and composition.

id : ∀ {s₁ s₂} {S : Setoid s₁ s₂} → LeftInverse S S
id {S = S} = record
  { to              = Eq.id
  ; from            = Eq.id
  ; left-inverse-of = λ _ → Setoid.refl S
  }
{-# WARNING_ON_USAGE id
"Warning: id was deprecated in v2.0.
Please use either Function.Properties.RightInverse.refl or
Function.Construct.Identity.rightInverse instead."
#-}

infixr 9 _∘_

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂}
        {F : Setoid f₁ f₂} {M : Setoid m₁ m₂} {T : Setoid t₁ t₂} →
      LeftInverse M T → LeftInverse F M → LeftInverse F T
_∘_ {F = F} f g = record
  { to              = to   f ⟪∘⟫ to   g
  ; from            = from g ⟪∘⟫ from f
  ; left-inverse-of = λ x → begin
      from g ⟨$⟩ (from f ⟨$⟩ (to f ⟨$⟩ (to g ⟨$⟩ x)))  ≈⟨ Eq.cong (from g) (left-inverse-of f (to g ⟨$⟩ x)) ⟩
      from g ⟨$⟩ (to g ⟨$⟩ x)                          ≈⟨ left-inverse-of g x ⟩
      x                                                ∎
  }
  where
  open LeftInverse
  open EqReasoning F
{-# WARNING_ON_USAGE _∘_
"Warning: _∘_ was deprecated in v2.0.
Please use either Function.Properties.RightInverse.trans or
Function.Construct.Composition.rightInverse instead."
#-}
