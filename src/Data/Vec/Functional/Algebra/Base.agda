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

module VecAddition (_∙_ : Op₂ A) where
  _∙ᴹ_ : Op₂ $ Vector A n
  _∙ᴹ_ = zipWith _∙_

module VecMagma (rawMagma : RawMagma a ℓ) where
  open RawMagma rawMagma public
  open VecAddition _∙_ public
  open EqualityVecFunc _≈_ public

module VecMonoid (rawMonoid : RawMonoid a ℓ) where
  open RawMonoid rawMonoid using (rawMagma; ε) public
  open VecMagma rawMagma public

  εᴹ : Vector Carrier n
  εᴹ = replicate ε

module VecGroup (rawGroup : RawGroup a ℓ) where
  open RawGroup rawGroup using (rawMonoid; _⁻¹) public
  open VecMonoid rawMonoid public

  -ᴹ_ : Op₁ $ Vector Carrier n
  -ᴹ_ = map $ _⁻¹

module VecNearSemiring (rawNearSemiring : RawNearSemiring a ℓ) where
  open RawNearSemiring rawNearSemiring using (+-rawMonoid; *-rawMagma) public
  open VecMonoid +-rawMonoid renaming (ε to 0#; εᴹ to 0ᴹ; _∙ᴹ_ to _+ᴹ_; _∙_ to _+_) public
  open VecMagma *-rawMagma public renaming (_∙ᴹ_ to _*ᴹ_; _∙_ to _*_) using ()

  _*ₗ_ : Opₗ Carrier (Vector Carrier n)
  _*ₗ_ r = map (r *_)

  _*ᵣ_ : Opᵣ Carrier (Vector Carrier n)
  _*ᵣ_ xs r = map (_* r) xs

module VecSemiring (rawSemiring : RawSemiring a ℓ) where
  open RawSemiring rawSemiring using (rawNearSemiring; 1#; *-rawMonoid) public
  open VecNearSemiring rawNearSemiring public
  open VecMonoid *-rawMonoid public renaming (εᴹ to 1ᴹ) using ()

module VecRing (rawRing : RawRing a ℓ) where
  open RawRing rawRing using (+-rawGroup; rawSemiring) public
  open VecGroup +-rawGroup public using (-ᴹ_)
  open VecSemiring rawSemiring public
