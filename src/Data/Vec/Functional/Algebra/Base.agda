------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vector-related module Definitions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Algebra.Base where

open import Level using (Level)
open import Function using (_$_)
open import Data.Product hiding (map)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec.Functional
open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Module
open import Relation.Binary
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as VecSetoid
import Algebra.Definitions as AD
import Algebra.Structures as AS

  -- {c ℓ} (cring : CommutativeRing c ℓ) where

private variable
  a ℓ : Level
  A : Set ℓ
  n : ℕ

-- open CommutativeRing cring
-- open VecSetoid setoid

module EqualityVecFunc (S : Setoid a ℓ) where
  open Setoid S
  open VecSetoid S

  _≈ᴹ_ : Rel (Vector Carrier n) ℓ
  _≈ᴹ_ = _≋_

_+ᴹ_ : (_+_ : Op₂ A) →  Op₂ $ Vector A n
_+ᴹ_ _+_ = zipWith _+_

_*ᴹ_ : (_*_ : Op₂ A) → Op₂ $ Vector A n
_*ᴹ_ _*_ = zipWith _*_

0ᴹ : A → Vector A n
0ᴹ 0# = replicate 0#

1ᴹ : A → Vector A n
1ᴹ 1# = replicate 1#

-ᴹ_ : Op₁ A → Op₁ $ Vector A n
-ᴹ_ -_ = map $ -_

_*ₗ_ : Op₂ A → Opₗ A (Vector A n)
_*ₗ_ _*_ r = map (r *_)

_*ᵣ_ : Op₂ A → Opᵣ A (Vector A n)
_*ᵣ_ _*_ xs r = map (_* r) xs
