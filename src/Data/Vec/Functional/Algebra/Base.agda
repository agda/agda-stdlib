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
  A : Set ℓ
  n : ℕ

-- Vector relation lifting
VecRel : {A : Set a} → Rel A ℓ → Rel (Vector A n) ℓ
VecRel _≈_ xs ys = Pointwise _≈_ xs ys

-- Binary operation lifting
lift₂ᴹ : {A : Set a} → Op₂ A → Op₂ (Vector A n)
lift₂ᴹ _∙_ = zipWith _∙_

-- Unary operation lifting
lift₁ᴹ : {A : Set a} → Op₁ A → Op₁ (Vector A n)
lift₁ᴹ f = map f

-- Vector RawMagma construction
VecRawMagma : RawMagma a ℓ → (n : ℕ) → RawMagma a ℓ
VecRawMagma M n =
  record
    { Carrier = Vector M.Carrier n
    ; _≈_ = VecRel M._≈_
    ; _∙_ = lift₂ᴹ M._∙_
    }
  where module M = RawMagma M

-- Vector RawMonoid construction
VecRawMonoid : RawMonoid a ℓ → (n : ℕ) → RawMonoid a ℓ
VecRawMonoid M n =
  record
    { RawMagma (VecRawMagma M.rawMagma n)
    ; ε  = λ _ → M.ε
    }
  where
    module M = RawMonoid M

-- Vector RawGroup construction
VecRawGroup : RawGroup a ℓ → (n : ℕ) → RawGroup a ℓ
VecRawGroup G n =
  record
    { RawMonoid (VecRawMonoid G.rawMonoid n)
    ; _⁻¹ = lift₁ᴹ G._⁻¹
    }
  where module G = RawGroup G

-- Vector RawNearSemiring construction
VecRawNearSemiring : RawNearSemiring a ℓ → (n : ℕ) → RawNearSemiring a ℓ
VecRawNearSemiring NS n =
  record
    { Carrier = Vector NS.Carrier n
    ; _≈_ = VecRel NS._≈_
    ; _+_ = lift₂ᴹ NS._+_
    ; _*_ = lift₂ᴹ NS._*_
    ; 0# = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS

-- Vector RawSemiring construction
VecRawSemiring : RawSemiring a ℓ → (n : ℕ) → RawSemiring a ℓ
VecRawSemiring S n =
  record
    { RawNearSemiring (VecRawNearSemiring S.rawNearSemiring n)
    ; 1# = λ _ → S.1#
    }
  where module S = RawSemiring S

-- Vector RawRing construction
VecRawRing : RawRing a ℓ → (n : ℕ) → RawRing a ℓ
VecRawRing R n =
  record
    { RawSemiring (VecRawSemiring R.rawSemiring n)
    ; -_ = lift₁ᴹ R.-_
    }
  where module R = RawRing R



-- Left scalar action obtained from the ring/semiring multiplication
_*ₗ_ : {S : Set a} → Op₂ S → Opₗ S (Vector S n)
_*ₗ_ _*_ r xs = map (λ x → _*_ r x) xs

-- Right scalar action (same underlying Op₂, but as a right action)
_*ᵣ_ : {S : Set a} → Op₂ S → Opᵣ S (Vector S n)
_*ᵣ_ _*_ xs r = map (λ x → _*_ x r) xs


VecRawLeftSemimodule : (NS : RawNearSemiring a ℓ) (n : ℕ) → RawLeftSemimodule (RawNearSemiring.Carrier NS) a ℓ
VecRawLeftSemimodule NS n =
  record
    { Carrierᴹ = Vector NS.Carrier n
    ; _≈ᴹ_     = VecRel NS._≈_
    ; _+ᴹ_     = lift₂ᴹ NS._+_
    ; _*ₗ_     = _*ₗ_ NS._*_
    ; 0ᴹ       = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS

VecRawRightSemimodule : (NS : RawNearSemiring a ℓ) (n : ℕ) → RawRightSemimodule (RawNearSemiring.Carrier NS) a ℓ
VecRawRightSemimodule NS n =
  record
    { Carrierᴹ = Vector NS.Carrier n
    ; _≈ᴹ_     = VecRel NS._≈_
    ; _+ᴹ_     = lift₂ᴹ NS._+_
    ; _*ᵣ_     = _*ᵣ_ NS._*_
    ; 0ᴹ       = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS

VecRawBisemimodule : (NS : RawNearSemiring a ℓ) (n : ℕ) → RawBisemimodule (RawNearSemiring.Carrier NS)
                    (RawNearSemiring.Carrier NS) a ℓ
VecRawBisemimodule NS n =
  record
    { Carrierᴹ = Vector NS.Carrier n
    ; _≈ᴹ_     = VecRel NS._≈_
    ; _+ᴹ_     = lift₂ᴹ NS._+_
    ; _*ₗ_     = _*ₗ_ NS._*_
    ; _*ᵣ_     = _*ᵣ_ NS._*_
    ; 0ᴹ       = λ _ → NS.0#
    }
  where module NS = RawNearSemiring NS
