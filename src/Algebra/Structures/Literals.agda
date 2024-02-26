------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebra Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles.Raw
open import Algebra.Structures.Pointed

module Algebra.Structures.Literals
  {c ℓ} {rawMonoid : RawMonoid c ℓ} {•}
  (isPointedMonoid : IsPointedMonoid rawMonoid •)
  where

open import Agda.Builtin.FromNat
open IsPointedMonoid isPointedMonoid

number : Number Carrier
number = record { Literals }
