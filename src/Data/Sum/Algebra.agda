------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic properties of sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Algebra where

open import Algebra
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_,_)
open import Data.Sum.Base
open import Data.Sum.Properties
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using (id; _∘_)
open import Function.Properties.Inverse using (↔-isEquivalence)
open import Function.Bundles using (_↔_; Inverse; mk↔′)
open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong′)

import Function.Definitions as FuncDef

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

  ♯ : {B : ⊥ {a} → Set b} → (w : ⊥) → B w
  ♯ ()

------------------------------------------------------------------------
-- Algebraic properties

⊎-cong : A ↔ B → C ↔ D → (A ⊎ C) ↔ (B ⊎ D)
⊎-cong i j = mk↔′ (map I.f J.f) (map I.f⁻¹ J.f⁻¹)
  [ cong inj₁ ∘ I.inverseˡ , cong inj₂ ∘ J.inverseˡ ]
  [ cong inj₁ ∘ I.inverseʳ , cong inj₂ ∘ J.inverseʳ ]
  where module I = Inverse i; module J = Inverse j

-- ⊎ is commutative.
-- We don't use Commutative because it isn't polymorphic enough.
⊎-comm : (A : Set a) (B : Set b) → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm _ _ = mk↔′ swap swap swap-involutive swap-involutive

module _ (ℓ : Level) where

  -- ⊎ is associative
  ⊎-assoc : Associative {ℓ = ℓ} _↔_ _⊎_
  ⊎-assoc _ _ _ = mk↔′ assocʳ assocˡ
    [ cong′ , [ cong′ , cong′ ] ] [ [ cong′ , cong′ ] , cong′ ]

  -- ⊥ is an identity for ⊎
  ⊎-identityˡ : LeftIdentity {ℓ = ℓ} _↔_ ⊥ _⊎_
  ⊎-identityˡ A = mk↔′ [ ♯ , id ] inj₂ cong′ [ ♯ , cong′ ]

  ⊎-identityʳ : RightIdentity {ℓ = ℓ} _↔_ ⊥ _⊎_
  ⊎-identityʳ _ = mk↔′ [ id , ♯ ] inj₁ cong′ [ cong′ , ♯ ]

  ⊎-identity : Identity _↔_ ⊥ _⊎_
  ⊎-identity = ⊎-identityˡ , ⊎-identityʳ

------------------------------------------------------------------------
-- Algebraic structures

  ⊎-isMagma : IsMagma {ℓ = ℓ} _↔_ _⊎_
  ⊎-isMagma = record
    { isEquivalence = ↔-isEquivalence
    ; ∙-cong        = ⊎-cong
    }

  ⊎-isSemigroup : IsSemigroup _↔_ _⊎_
  ⊎-isSemigroup = record
    { isMagma = ⊎-isMagma
    ; assoc   = ⊎-assoc
    }

  ⊎-isMonoid : IsMonoid _↔_ _⊎_ ⊥
  ⊎-isMonoid = record
    { isSemigroup = ⊎-isSemigroup
    ; identity    = ⊎-identityˡ , ⊎-identityʳ
    }

  ⊎-isCommutativeMonoid : IsCommutativeMonoid _↔_ _⊎_ ⊥
  ⊎-isCommutativeMonoid = record
    { isMonoid = ⊎-isMonoid
    ; comm     = ⊎-comm
    }

------------------------------------------------------------------------
-- Algebraic bundles

  ⊎-magma : Magma (suc ℓ) ℓ
  ⊎-magma = record
    { isMagma = ⊎-isMagma
    }

  ⊎-semigroup : Semigroup (suc ℓ) ℓ
  ⊎-semigroup = record
    { isSemigroup = ⊎-isSemigroup
    }

  ⊎-monoid : Monoid (suc ℓ) ℓ
  ⊎-monoid = record
    { isMonoid = ⊎-isMonoid
    }

  ⊎-commutativeMonoid : CommutativeMonoid (suc ℓ) ℓ
  ⊎-commutativeMonoid = record
    { isCommutativeMonoid = ⊎-isCommutativeMonoid
    }
