------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vector-related module Definitions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Algebra.Base where

open import Level using (Level; suc; _⊔_)
open import Function using (_$_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec.Functional
open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Module
open import Relation.Binary using (Rel)
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)

private variable
  a ℓ : Level
  A : Set a
  n : ℕ

------------------------------------------------------------------------
-- Vector-lifted relations & operators

pointwiseᵛ : ( _≈_ : Rel A ℓ ) → Rel (Vector A n) ℓ
pointwiseᵛ _≈_ = Pointwise _≈_

zipWithᵛ : Op₂ A → Op₂ (Vector A n)
zipWithᵛ _∙_ = zipWith _∙_

mapᵛ : Op₁ A → Op₁ (Vector A n)
mapᵛ f = map f

------------------------------------------------------------------------
-- Vector-lifted raw structures

rawMagmaᵛ : RawMagma a ℓ → (n : ℕ) → RawMagma a ℓ
rawMagmaᵛ M n =
  record
    { Carrier = Vector M.Carrier n
    ; _≈_     = pointwiseᵛ M._≈_
    ; _∙_     = zipWithᵛ M._∙_
    }
  where module M = RawMagma M

rawMonoidᵛ : RawMonoid a ℓ → (n : ℕ) → RawMonoid a ℓ
rawMonoidᵛ M n =
  record
    { RawMagma (rawMagmaᵛ M.rawMagma n)
    ; ε = λ _ → M.ε
    }
  where module M = RawMonoid M

rawGroupᵛ : RawGroup a ℓ → (n : ℕ) → RawGroup a ℓ
rawGroupᵛ G n =
  record
    { RawMonoid (rawMonoidᵛ G.rawMonoid n)
    ; _⁻¹ = mapᵛ G._⁻¹
    }
  where module G = RawGroup G

rawNearSemiringᵛ : RawNearSemiring a ℓ → (n : ℕ) → RawNearSemiring a ℓ
rawNearSemiringᵛ NS n =
  record
    { Carrier = Vector NS.Carrier n
    ; _≈_     = pointwiseᵛ NS._≈_
    ; _+_     = zipWithᵛ NS._+_
    ; _*_     = zipWithᵛ NS._*_
    ; 0#      = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS

rawSemiringᵛ : RawSemiring a ℓ → (n : ℕ) → RawSemiring a ℓ
rawSemiringᵛ S n =
  record
    { RawNearSemiring (rawNearSemiringᵛ S.rawNearSemiring n)
    ; 1# = λ _ → S.1#
    }
  where module S = RawSemiring S

rawRingᵛ : RawRing a ℓ → (n : ℕ) → RawRing a ℓ
rawRingᵛ R n =
  record
    { RawSemiring (rawSemiringᵛ R.rawSemiring n)
    ; -_ = mapᵛ R.-_
    }
  where module R = RawRing R

------------------------------------------------------------------------
-- Vector actions (left/right scalar multiplication)

_*ₗᵛ_ : {S : Set a} → Op₂ S → Opₗ S (Vector S n)
_*ₗᵛ_ _*_ r xs = map (r *_) xs

_*ᵣᵛ_ : {S : Set a} → Op₂ S → Opᵣ S (Vector S n)
_*ᵣᵛ_ _*_ xs r = map (_* r) xs

------------------------------------------------------------------------
-- Vector-lifted semimodule bundles

rawLeftSemimoduleᵛ : (NS : RawNearSemiring a ℓ) (n : ℕ) → RawLeftSemimodule (RawNearSemiring.Carrier NS) a ℓ
rawLeftSemimoduleᵛ NS n =
  record
    { Carrierᴹ = Vector NS.Carrier n
    ; _≈ᴹ_     = pointwiseᵛ NS._≈_
    ; _+ᴹ_     = zipWithᵛ NS._+_
    ; _*ₗ_     = _*ₗᵛ_ NS._*_
    ; 0ᴹ       = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS

rawRightSemimoduleᵛ : (NS : RawNearSemiring a ℓ) (n : ℕ) → RawRightSemimodule (RawNearSemiring.Carrier NS) a ℓ
rawRightSemimoduleᵛ NS n =
  record
    { Carrierᴹ = Vector NS.Carrier n
    ; _≈ᴹ_     = pointwiseᵛ NS._≈_
    ; _+ᴹ_     = zipWithᵛ NS._+_
    ; _*ᵣ_     = _*ᵣᵛ_ NS._*_
    ; 0ᴹ       = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS

rawBisemimoduleᵛ : (NS : RawNearSemiring a ℓ) (n : ℕ) → RawBisemimodule (RawNearSemiring.Carrier NS)
                   (RawNearSemiring.Carrier NS) a ℓ
rawBisemimoduleᵛ NS n =
  record
    { Carrierᴹ = Vector NS.Carrier n
    ; _≈ᴹ_     = pointwiseᵛ NS._≈_
    ; _+ᴹ_     = zipWithᵛ NS._+_
    ; _*ₗ_     = _*ₗᵛ_ NS._*_
    ; _*ᵣ_     = _*ᵣᵛ_ NS._*_
    ; 0ᴹ       = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS