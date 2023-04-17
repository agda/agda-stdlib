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

_≈ᴹ_ : Rel (Vector Carrier n) ℓ
_≈ᴹ_ = _≋_

_+ᴹ_ : Op₂ $ Vector Carrier n
_+ᴹ_ = zipWith _+_

0ᴹ : Vector Carrier n
0ᴹ = replicate 0#

-ᴹ_ : Op₁ $ Vector Carrier n
-ᴹ_ = map $ -_

_*ₗ_ : Opₗ Carrier (Vector Carrier n)
_*ₗ_ r = map (r *_)

_*ᵣ_ : Opᵣ Carrier (Vector Carrier n)
xs *ᵣ r = map (_* r) xs
