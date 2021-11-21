------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by lattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.Lattice
  {c ℓ₁ ℓ₂} (L : Lattice c ℓ₁ ℓ₂) where

open Lattice L

import Algebra.Lattice as Alg
open import Algebra.Definitions _≈_
open import Data.Product using (_,_)
open import Function.Base using (flip)
open import Relation.Binary
open import Relation.Binary.Properties.Poset poset
import Relation.Binary.Lattice.Properties.JoinSemilattice joinSemilattice as J
import Relation.Binary.Lattice.Properties.MeetSemilattice meetSemilattice as M
import Relation.Binary.Reasoning.Setoid as EqReasoning
import Relation.Binary.Reasoning.PartialOrder as POR

open import Relation.Binary.Lattice.Properties.Lattice

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.Lattice was deprecated in v2.0.
Use Relation.Binary.Properties.Lattice instead."
#-}

