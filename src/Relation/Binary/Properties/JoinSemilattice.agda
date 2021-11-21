------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by join semilattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.JoinSemilattice
  {c ℓ₁ ℓ₂} (J : JoinSemilattice c ℓ₁ ℓ₂) where

open JoinSemilattice J

import Algebra.Lattice as Alg
open import Algebra.Definitions _≈_
open import Data.Product
open import Function.Base using (_∘_; flip)
open import Relation.Binary
open import Relation.Binary.Properties.Poset poset

import Relation.Binary.Reasoning.PartialOrder as PoR

open import Relation.Binary.Lattice.Properties.JoinSemilattice

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.JoinSemilattice was deprecated in v2.0.
Use Relation.Binary.Properties.JoinSemilattice instead."
#-}
