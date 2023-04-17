------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vector-related module Definitions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

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

module Data.Vec.Functional.Algebra.Base
  {c ℓ} (ring : Ring c ℓ) where

private variable
  n : ℕ

open Ring ring
open VecSetoid setoid

VC = Vector Carrier

_≈ᴹ_ : Rel (VC n) ℓ
_≈ᴹ_ = _≋_

_+ᴹ_ : Op₂ $ VC n
_+ᴹ_ = zipWith _+_

0ᴹ : VC n
0ᴹ = replicate 0#

-ᴹ_ : Op₁ $ VC n
-ᴹ_ = map $ -_

_*ₗ_ : Opₗ Carrier (VC n)
_*ₗ_ r = map (r *_)
