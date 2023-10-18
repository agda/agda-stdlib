------------------------------------------------------------------------
-- The Agda standard library
--
-- The constant function
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Construct.Constant where

open import Function.Base using (const)
open import Function.Bundles
import Function.Definitions as Definitions
import Function.Structures as Structures
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures as B hiding (IsEquivalence)

private
  variable
    a b ℓ₁ ℓ₂ : Level
    A B : Set a

------------------------------------------------------------------------
-- Properties

module _ (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂) where

  open Definitions

  congruent : ∀ {b} → b ≈₂ b → Congruent _≈₁_ _≈₂_ (const b)
  congruent refl _ = refl

------------------------------------------------------------------------
-- Structures

module _
  {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂}
  (isEq₁ : B.IsEquivalence ≈₁)
  (isEq₂ : B.IsEquivalence ≈₂) where

  open Structures ≈₁ ≈₂
  open B.IsEquivalence

  isCongruent : ∀ b → IsCongruent (const b)
  isCongruent b = record
    { cong           = congruent ≈₁ ≈₂ (refl isEq₂)
    ; isEquivalence₁ = isEq₁
    ; isEquivalence₂ = isEq₂
    }

------------------------------------------------------------------------
-- Setoid bundles

module _ (S : Setoid a ℓ₂) (T : Setoid b ℓ₂) where

  open Setoid

  function : Carrier T → Func S T
  function b = record
    { to   = const b
    ; cong = congruent (_≈_ S) (_≈_ T) (refl T)
    }
