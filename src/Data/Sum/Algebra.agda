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

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong′)

------------------------------------------------------------------------
-- Setup

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

  ♯ : {B : ⊥ {a} → Set b} → (w : ⊥) → B w
  ♯ ()

------------------------------------------------------------------------
-- Algebraic properties

-- ⊎ is associative
⊎-assoc : ∀ ℓ → Associative {ℓ = ℓ} _↔_ _⊎_
⊎-assoc ℓ _ _ _ = inverse assocʳ assocˡ
  [ cong′ , [ cong′ , cong′ ] ] [ [ cong′ , cong′ ] , cong′ ]

-- ⊎ is commutative.
-- We don't use Commutative because it isn't polymorphic enough.
⊎-comm : (A : Set a) (B : Set b) → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm _ _ = inverse swap swap swap-involutive swap-involutive

-- ⊥ is both left and right identity for ⊎
⊎-identityˡ : ∀ ℓ → LeftIdentity _↔_ (⊥ {ℓ}) _⊎_
⊎-identityˡ ℓ A = inverse [ ♯ , id ] inj₂ cong′ [ ♯ , cong′ ]

⊎-identityʳ : ∀ ℓ → RightIdentity _↔_ (⊥ {ℓ}) _⊎_
⊎-identityʳ _ _ = inverse [ id , ♯ ] inj₁ cong′ [ cong′ , ♯ ]

⊎-identity : ∀ ℓ → Identity _↔_ (⊥ {ℓ}) _⊎_
⊎-identity ℓ = ⊎-identityˡ ℓ , ⊎-identityʳ ℓ

⊎-cong : A ↔ B → C ↔ D → (A ⊎ C) ↔ (B ⊎ D)
⊎-cong i j = inverse (map I.f J.f) (map I.f⁻¹ J.f⁻¹)
  [ cong inj₁ ∘ I.inverseˡ , cong inj₂ ∘ J.inverseˡ ]
  [ cong inj₁ ∘ I.inverseʳ , cong inj₂ ∘ J.inverseʳ ]
  where module I = Inverse i; module J = Inverse j

------------------------------------------------------------------------
-- Algebraic structures

module _ (ℓ : Level) where

  ⊎-isMagma : IsMagma {ℓ = ℓ} _↔_ _⊎_
  ⊎-isMagma = record
    { isEquivalence = ↔-isEquivalence
    ; ∙-cong        = ⊎-cong
    }

  ⊎-isSemigroup : IsSemigroup _↔_ _⊎_
  ⊎-isSemigroup = record
    { isMagma = ⊎-isMagma
    ; assoc   = λ _ _ _ → ⊎-assoc _ _ _ _
    }

  ⊎-isMonoid : IsMonoid _↔_ _⊎_ ⊥
  ⊎-isMonoid = record
    { isSemigroup = ⊎-isSemigroup
    ; identity    = ⊎-identityˡ ℓ , ⊎-identityʳ ℓ
    }

  ⊎-isCommutativeMonoid : IsCommutativeMonoid _↔_ _⊎_ ⊥
  ⊎-isCommutativeMonoid = record
    { isMonoid = ⊎-isMonoid
    ; comm     = ⊎-comm
    }

------------------------------------------------------------------------
-- Algebraic bundles

  ⊎-magma : Magma _ _
  ⊎-magma = record
    { isMagma = ⊎-isMagma
    }

  ⊎-semigroup : Semigroup _ _
  ⊎-semigroup = record
    { isSemigroup = ⊎-isSemigroup
    }

  ⊎-monoid : Monoid _ _
  ⊎-monoid = record
    { isMonoid = ⊎-isMonoid
    }

  ⊎-commutativeMonoid : CommutativeMonoid _ _
  ⊎-commutativeMonoid = record
    { isCommutativeMonoid = ⊎-isCommutativeMonoid
    }
