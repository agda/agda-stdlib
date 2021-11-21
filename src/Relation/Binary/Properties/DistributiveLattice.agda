------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties for distributive lattice
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.DistributiveLattice
  {c ℓ₁ ℓ₂} (L : DistributiveLattice c ℓ₁ ℓ₂) where

open DistributiveLattice L hiding (refl)

open import Algebra.Definitions _≈_
open import Data.Product using (_,_)
open import Relation.Binary
open import Relation.Binary.Reasoning.Setoid setoid
open import Relation.Binary.Properties.Lattice lattice
open import Relation.Binary.Properties.MeetSemilattice meetSemilattice
open import Relation.Binary.Properties.JoinSemilattice joinSemilattice

open Setoid setoid

open import Relation.Binary.Lattice.Properties.DistributiveLattice

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.DistributiveLattice was deprecated in v2.0.
Use Relation.Binary.Properties.DistributiveLattice instead."
#-}
