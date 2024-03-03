------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warn=noUserWarning #-}

module Function.Equivalence where

{-# WARNING_ON_IMPORT
"Function.Equivalence was deprecated in v2.0.
Use the standard function hierarchy in Function/Function.Bundles instead."
#-}

open import Function.Base using (flip)
open import Function.Equality as F
  using (_⟶_; _⟨$⟩_; →-to-⟶) renaming (_∘_ to _⟪∘⟫_)
open import Level
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; TransFlip; Sym)
import Relation.Binary.PropositionalEquality as ≡

------------------------------------------------------------------------
-- Setoid equivalence

record Equivalence {f₁ f₂ t₁ t₂}
                   (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                   Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to   : From ⟶ To
    from : To ⟶ From
{-# WARNING_ON_USAGE Equivalence
"Warning: Equivalence was deprecated in v2.0.
Please use Function.(Bundles.)Equivalence instead."
#-}

------------------------------------------------------------------------
-- The set of all equivalences between two sets (i.e. equivalences
-- with propositional equality)

infix 3 _⇔_

_⇔_ : ∀ {f t} → Set f → Set t → Set _
From ⇔ To = Equivalence (≡.setoid From) (≡.setoid To)
{-# WARNING_ON_USAGE _⇔_
"Warning: _⇔_ was deprecated in v2.0.
Please use Function.(Bundles.)_⇔_ instead."
#-}

equivalence : ∀ {f t} {From : Set f} {To : Set t} →
              (From → To) → (To → From) → From ⇔ To
equivalence to from = record
  { to   = →-to-⟶ to
  ; from = →-to-⟶ from
  }
{-# WARNING_ON_USAGE equivalence
"Warning: equivalence was deprecated in v2.0.
Please use Function.Properties.Equivalence.mkEquivalence instead."
#-}

------------------------------------------------------------------------
-- Equivalence is an equivalence relation

-- Identity and composition (reflexivity and transitivity).

id : ∀ {s₁ s₂} → Reflexive (Equivalence {s₁} {s₂})
id {x = S} = record
  { to   = F.id
  ; from = F.id
  }
{-# WARNING_ON_USAGE id
"Warning: id was deprecated in v2.0.
Please use Function.Properties.Equivalence.refl or
Function.Construct.Identity.equivalence instead."
#-}

infixr 9 _∘_

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂} →
      TransFlip (Equivalence {f₁} {f₂} {m₁} {m₂})
                (Equivalence {m₁} {m₂} {t₁} {t₂})
                (Equivalence {f₁} {f₂} {t₁} {t₂})
f ∘ g = record
  { to   = to   f ⟪∘⟫ to   g
  ; from = from g ⟪∘⟫ from f
  } where open Equivalence
{-# WARNING_ON_USAGE _∘_
"Warning: _∘_ was deprecated in v2.0.
Please use Function.Properties.Equivalence.trans or
Function.Construct.Composition.equivalence instead."
#-}

-- Symmetry.

sym : ∀ {f₁ f₂ t₁ t₂} →
      Sym (Equivalence {f₁} {f₂} {t₁} {t₂})
          (Equivalence {t₁} {t₂} {f₁} {f₂})
sym eq = record
  { from       = to
  ; to         = from
  } where open Equivalence eq
{-# WARNING_ON_USAGE sym
"Warning: sym was deprecated in v2.0.
Please use Function.Properties.Equivalence.sym or
Function.Construct.Symmetry.equivalence instead."
#-}

-- For fixed universe levels we can construct setoids.

setoid : (s₁ s₂ : Level) → Setoid (suc (s₁ ⊔ s₂)) (s₁ ⊔ s₂)
setoid s₁ s₂ = record
  { Carrier       = Setoid s₁ s₂
  ; _≈_           = Equivalence
  ; isEquivalence = record
    { refl  = id
    ; sym   = sym
    ; trans = flip _∘_
    }
  }
{-# WARNING_ON_USAGE setoid
"Warning: setoid was deprecated in v2.0.
Please use Function.Properties.Equivalence.setoid instead."
#-}

⇔-setoid : (ℓ : Level) → Setoid (suc ℓ) ℓ
⇔-setoid ℓ = record
  { Carrier       = Set ℓ
  ; _≈_           = _⇔_
  ; isEquivalence = record
    { refl  = id
    ; sym   = sym
    ; trans = flip _∘_
    }
  }
{-# WARNING_ON_USAGE ⇔-setoid
"Warning: ⇔-setoid was deprecated in v2.0.
Please use Function.Properties.Equivalence.⇔-setoid instead."
#-}

------------------------------------------------------------------------
-- Transformations

map : ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
        {f₁′ f₂′ t₁′ t₂′}
        {From′ : Setoid f₁′ f₂′} {To′ : Setoid t₁′ t₂′} →
      ((From ⟶ To) → (From′ ⟶ To′)) →
      ((To ⟶ From) → (To′ ⟶ From′)) →
      Equivalence From To → Equivalence From′ To′
map t f eq = record { to = t to; from = f from }
  where open Equivalence eq

zip : ∀ {f₁₁ f₂₁ t₁₁ t₂₁}
        {From₁ : Setoid f₁₁ f₂₁} {To₁ : Setoid t₁₁ t₂₁}
        {f₁₂ f₂₂ t₁₂ t₂₂}
        {From₂ : Setoid f₁₂ f₂₂} {To₂ : Setoid t₁₂ t₂₂}
        {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
      ((From₁ ⟶ To₁) → (From₂ ⟶ To₂) → (From ⟶ To)) →
      ((To₁ ⟶ From₁) → (To₂ ⟶ From₂) → (To ⟶ From)) →
      Equivalence From₁ To₁ → Equivalence From₂ To₂ →
      Equivalence From To
zip t f eq₁ eq₂ =
  record { to = t (to eq₁) (to eq₂); from = f (from eq₁) (from eq₂) }
  where open Equivalence
