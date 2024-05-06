------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic properties of sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Sum.Algebra where

open import Algebra.Bundles
  using (Magma; Semigroup; Monoid; CommutativeMonoid)
open import Algebra.Definitions
open import Algebra.Structures
  using (IsMagma; IsSemigroup; IsMonoid; IsCommutativeMonoid)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; map; [_,_]; swap; assocʳ; assocˡ)
open import Data.Sum.Properties using (swap-involutive)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Function.Base using (id; _∘_)
open import Function.Properties.Inverse using (↔-isEquivalence)
open import Function.Bundles using (_↔_; Inverse; mk↔ₛ′)
open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong′)

import Function.Definitions as FuncDef

------------------------------------------------------------------------
-- Setup

private
  variable
    a b c d : Level
    A B C D : Set a

  ♯ : {B : ⊥ {a} → Set b} → (w : ⊥) → B w
  ♯ ()

------------------------------------------------------------------------
-- Algebraic properties

⊎-cong : A ↔ B → C ↔ D → (A ⊎ C) ↔ (B ⊎ D)
⊎-cong i j = mk↔ₛ′ (map I.to J.to) (map I.from J.from)
  [ cong inj₁ ∘ I.strictlyInverseˡ , cong inj₂ ∘ J.strictlyInverseˡ ]
  [ cong inj₁ ∘ I.strictlyInverseʳ , cong inj₂ ∘ J.strictlyInverseʳ ]
  where module I = Inverse i; module J = Inverse j

-- ⊎ is commutative.
-- We don't use Commutative because it isn't polymorphic enough.
⊎-comm : (A : Set a) (B : Set b) → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm _ _ = mk↔ₛ′ swap swap swap-involutive swap-involutive

module _ (ℓ : Level) where

  -- ⊎ is associative
  ⊎-assoc : Associative {ℓ = ℓ} _↔_ _⊎_
  ⊎-assoc _ _ _ = mk↔ₛ′ assocʳ assocˡ
    [ cong′ , [ cong′ , cong′ ] ] [ [ cong′ , cong′ ] , cong′ ]

  -- ⊥ is an identity for ⊎
  ⊎-identityˡ : LeftIdentity {ℓ = ℓ} _↔_ ⊥ _⊎_
  ⊎-identityˡ A = mk↔ₛ′ [ ♯ , id ] inj₂ cong′ [ ♯ , cong′ ]

  ⊎-identityʳ : RightIdentity {ℓ = ℓ} _↔_ ⊥ _⊎_
  ⊎-identityʳ _ = mk↔ₛ′ [ id , ♯ ] inj₁ cong′ [ cong′ , ♯ ]

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
