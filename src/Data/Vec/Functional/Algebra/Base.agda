------------------------------------------------------------------------
-- The Agda standard library
--
-- Some VecF.Vector-related module Definitions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Algebra.Base where

open import Level using (Level; suc; _⊔_)
open import Function using (_$_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Vec.Functional as VecF
open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Module
open import Relation.Binary using (Rel)
import Data.Vec.Functional.Relation.Binary.Pointwise as Pointwise

private variable
  a ℓ : Level
  A : Set a
  n : ℕ

------------------------------------------------------------------------
-- VecF.Vector-lifted raw structures

rawMagma : RawMagma a ℓ → (n : ℕ) → RawMagma a ℓ
rawMagma M n =
  record
    { Carrier = VecF.Vector M.Carrier n
    ; _≈_     = Pointwise.Pointwise M._≈_
    ; _∙_     = VecF.zipWith M._∙_
    }
  where module M = RawMagma M

rawMonoid : RawMonoid a ℓ → (n : ℕ) → RawMonoid a ℓ
rawMonoid M n =
  record
    { RawMagma (rawMagma M.rawMagma n)
    ; ε = λ _ → M.ε
    }
  where module M = RawMonoid M

rawGroup : RawGroup a ℓ → (n : ℕ) → RawGroup a ℓ
rawGroup G n =
  record
    { RawMonoid (rawMonoid G.rawMonoid n)
    ; _⁻¹ = VecF.map G._⁻¹
    }
  where module G = RawGroup G

rawNearSemiring : RawNearSemiring a ℓ → (n : ℕ) → RawNearSemiring a ℓ
rawNearSemiring NS n =
  record
    { Carrier = VecF.Vector NS.Carrier n
    ; _≈_     = Pointwise.Pointwise NS._≈_
    ; _+_     = VecF.zipWith NS._+_
    ; _*_     = VecF.zipWith NS._*_
    ; 0#      = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS

rawSemiring : RawSemiring a ℓ → (n : ℕ) → RawSemiring a ℓ
rawSemiring S n =
  record
    { RawNearSemiring (rawNearSemiring S.rawNearSemiring n)
    ; 1# = λ _ → S.1#
    }
  where module S = RawSemiring S

rawRing : RawRing a ℓ → (n : ℕ) → RawRing a ℓ
rawRing R n =
  record
    { RawSemiring (rawSemiring R.rawSemiring n)
    ; -_ = VecF.map R.-_
    }
  where module R = RawRing R

------------------------------------------------------------------------
-- VecF.Vector actions (left/right scalar multiplication)

_*ₗ_ : {S : Set a} → Op₂ S → Opₗ S (VecF.Vector S n)
_*ₗ_ _*_ r xs = VecF.map (r *_) xs

_*ᵣ_ : {S : Set a} → Op₂ S → Opᵣ S (VecF.Vector S n)
_*ᵣ_ _*_ xs r = VecF.map (_* r) xs

------------------------------------------------------------------------
-- VecF.Vector-lifted semimodule bundles

rawLeftSemimodule : (NS : RawNearSemiring a ℓ) (n : ℕ) → RawLeftSemimodule (RawNearSemiring.Carrier NS) a ℓ
rawLeftSemimodule NS n =
  record
    { Carrierᴹ = VecF.Vector NS.Carrier n
    ; _≈ᴹ_     = Pointwise.Pointwise NS._≈_
    ; _+ᴹ_     = VecF.zipWith NS._+_
    ; _*ₗ_     = _*ₗ_ NS._*_
    ; 0ᴹ       = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS

rawRightSemimodule : (NS : RawNearSemiring a ℓ) (n : ℕ) → RawRightSemimodule (RawNearSemiring.Carrier NS) a ℓ
rawRightSemimodule NS n =
  record
    { Carrierᴹ = VecF.Vector NS.Carrier n
    ; _≈ᴹ_     = Pointwise.Pointwise NS._≈_
    ; _+ᴹ_     = VecF.zipWith NS._+_
    ; _*ᵣ_     = _*ᵣ_ NS._*_
    ; 0ᴹ       = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS

rawBisemimodule : (NS : RawNearSemiring a ℓ) (n : ℕ) → RawBisemimodule (RawNearSemiring.Carrier NS)
                   (RawNearSemiring.Carrier NS) a ℓ
rawBisemimodule NS n =
  record
    { Carrierᴹ = VecF.Vector NS.Carrier n
    ; _≈ᴹ_     = Pointwise.Pointwise NS._≈_
    ; _+ᴹ_     = VecF.zipWith NS._+_
    ; _*ₗ_     = _*ₗ_ NS._*_
    ; _*ᵣ_     = _*ᵣ_ NS._*_
    ; 0ᴹ       = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS
