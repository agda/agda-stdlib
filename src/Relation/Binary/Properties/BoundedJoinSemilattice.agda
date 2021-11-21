------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded join semilattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.BoundedJoinSemilattice
  {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open BoundedJoinSemilattice J

open import Algebra.Definitions _≈_
open import Data.Product
open import Function.Base using (_∘_; flip)
open import Relation.Binary
open import Relation.Binary.Properties.Poset poset

open import Relation.Binary.Lattice.Properties.BoundedJoinSemilattice

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.BoundedJoinSemilattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.BoundedJoinSemilattice instead."
#-}
