------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic properties of sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Algebra where

open import Agda.Builtin.Sigma
open import Algebra
open import Data.Empty.Polymorphic using (⊥)
open import Data.Sum.Base
open import Data.Sum.Properties
open import Function.Base using (id; _∘_)
open import Function.Properties.Inverse using (↔-isEquivalence)
open import Level using (Level)

open import Function.Bundles using (_↔_; Inverse; mk↔)
import Function.Definitions as FuncDef

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)

------------------------------------------------------------------------

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

-- The module is needed because we need to pass `A` and `B` to `FuncDef`
module _ {A : Set a} {B : Set b} where
  open FuncDef {A = A} {B} _≡_ _≡_

  -- mk↔ is a bit of a pain to use because here f and f⁻¹ need to always
  -- be specified.
  inverse : (f : A → B) (f⁻¹ : B → A) → Inverseˡ f f⁻¹ → Inverseʳ f f⁻¹ → A ↔ B
  inverse f f⁻¹ left right = mk↔ {f = f} {f⁻¹} (left , right)

private
  -- convenient abbreviations
  irefl : {A : Set a} {B : Set b} {f : A → B} (x : A) → f x ≡ f x
  irefl _ = refl

  ♯ : {B : ⊥ {a} → Set b} → (w : ⊥) → B w
  ♯ ()

------------------------------------------------------------------------
-- Properties of ⊎

-- ⊎ is associative

⊎-assoc : ∀ ℓ → Associative {ℓ = ℓ} _↔_ _⊎_
⊎-assoc ℓ _ _ _ = inverse assocʳ assocˡ [ irefl , [ irefl , irefl ] ] [ [ irefl , irefl ] , irefl ]

-- ⊎ is commutative.
-- We don't use Commutative because it isn't polymorphic enough.

⊎-comm : (A : Set a) (B : Set b) → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm _ _ = inverse swap swap swap-involutive swap-involutive

-- ⊥ is both left and right identity for ⊎
⊎-identityˡ : ∀ ℓ → LeftIdentity _↔_ (⊥ {ℓ}) _⊎_
⊎-identityˡ ℓ A = inverse [ ♯ , id ] inj₂ irefl [ ♯ , irefl ]

⊎-identityʳ : ∀ ℓ → RightIdentity _↔_ (⊥ {ℓ}) _⊎_
⊎-identityʳ _ _ = inverse [ id , ♯ ] inj₁ irefl [ irefl , ♯ ]

⊎-identity : ∀ ℓ → Identity _↔_ (⊥ {ℓ}) _⊎_
⊎-identity ℓ = ⊎-identityˡ ℓ , ⊎-identityʳ ℓ

infix 4 _⊎-cong_

_⊎-cong_ : A ↔ B → C ↔ D → (A ⊎ C) ↔ (B ⊎ D)
i ⊎-cong j = inverse (map I.f J.f) (map I.f⁻¹ J.f⁻¹)
  [ cong inj₁ ∘ I.inverseˡ , cong inj₂ ∘ J.inverseˡ ]
  [ cong inj₁ ∘ I.inverseʳ , cong inj₂ ∘ J.inverseʳ ]
  where
  module I = Inverse i
  module J = Inverse j

------------------------------------------------------------------------
-- ⊥, _⊎_ form a commutative monoid

⊎-isMagma : ∀ ℓ → IsMagma {Level.suc ℓ} _↔_ _⊎_
⊎-isMagma ℓ = record
  { isEquivalence = ↔-isEquivalence
  ; ∙-cong        = _⊎-cong_
  }

⊎-magma : (ℓ : Level) → Magma _ _
⊎-magma ℓ = record
  { isMagma = ⊎-isMagma ℓ
  }

⊎-isSemigroup : ∀ ℓ → IsSemigroup {Level.suc ℓ} _↔_ _⊎_
⊎-isSemigroup ℓ = record
  { isMagma = ⊎-isMagma ℓ
  ; assoc   = λ _ _ _ → ⊎-assoc _ _ _ _
  }

⊎-semigroup : (ℓ : Level) → Semigroup _ _
⊎-semigroup ℓ = record
  { isSemigroup = ⊎-isSemigroup ℓ
  }

⊎-isMonoid : ∀ ℓ → IsMonoid _↔_ _⊎_ ⊥
⊎-isMonoid ℓ = record
  { isSemigroup = ⊎-isSemigroup ℓ
  ; identity    = (⊎-identityˡ ℓ) , (⊎-identityʳ ℓ)
  }

⊎-monoid : (ℓ : Level) → Monoid _ _
⊎-monoid ℓ = record
  { isMonoid = ⊎-isMonoid ℓ
  }

⊎-isCommutativeMonoid : ∀ ℓ → IsCommutativeMonoid _↔_ _⊎_ ⊥
⊎-isCommutativeMonoid ℓ = record
  { isMonoid = ⊎-isMonoid ℓ
  ; comm     = ⊎-comm
  }

⊎-commutativeMonoid : (ℓ : Level) → CommutativeMonoid _ _
⊎-commutativeMonoid ℓ = record
  { isCommutativeMonoid = ⊎-isCommutativeMonoid ℓ
  }
