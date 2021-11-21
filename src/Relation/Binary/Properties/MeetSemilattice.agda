------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by meet semilattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.MeetSemilattice
  {c ℓ₁ ℓ₂} (M : MeetSemilattice c ℓ₁ ℓ₂) where

open MeetSemilattice M

open import Algebra.Definitions _≈_
open import Data.Product
open import Function.Base using (flip)
open import Relation.Binary
open import Relation.Binary.Properties.Poset poset
import Relation.Binary.Lattice.Properties.JoinSemilattice as J

open import Relation.Binary.Lattice.Properties.MeetSemilattice

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.MeetSemilattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.MeetSemilattice instead."
#-}

