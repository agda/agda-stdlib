------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vector-related module Definitions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Algebra.Base where

open import Level using (Level)
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

module EqualityVecFunc (_≈_ : Rel A ℓ) where
  _≈ᴹ_ : Rel (Vector A n) ℓ
  _≈ᴹ_ = Pointwise _≈_

module VecAddition (_+_ : Op₂ A) where
  _+ᴹ_ : Op₂ $ Vector A n
  _+ᴹ_ = zipWith _+_

module VecMagma (rawMagma : RawMagma a ℓ) where
  open RawMagma rawMagma
  open VecAddition _∙_ public
  open EqualityVecFunc _≈_ public

module VecMonoid (rawMonoid : RawMonoid a ℓ) where
  open RawMonoid rawMonoid
  open VecMagma rawMagma public

  0ᴹ : Vector Carrier n
  0ᴹ = replicate ε

module VecGroup (rawGroup : RawGroup a ℓ) where
  open RawGroup rawGroup
  open VecMonoid rawMonoid public

  -ᴹ_ : Op₁ $ Vector Carrier n
  -ᴹ_ = map $ _⁻¹

module VecNearSemiring (rawNearSemiring : RawNearSemiring a ℓ) where
  open RawNearSemiring rawNearSemiring
  open VecMonoid +-rawMonoid public
  open VecMagma *-rawMagma public renaming (_+ᴹ_ to _*ᴹ_) using ()

module VecSemiring (rawSemiring : RawSemiring a ℓ) where
  open RawSemiring rawSemiring
  open VecNearSemiring rawNearSemiring public

  1ᴹ : Vector Carrier n
  1ᴹ = replicate 1#

  _*ₗ_ : Op₂ A → Opₗ A (Vector A n)
  _*ₗ_ _*_ r = map (r *_)

  _*ᵣ_ : Op₂ A → Opᵣ A (Vector A n)
  _*ᵣ_ _*_ xs r = map (_* r) xs

module VecRing (rawRing : RawRing a ℓ) where
  open RawRing rawRing
  open VecGroup +-rawGroup public using (-ᴹ_)
  open VecSemiring rawSemiring public
