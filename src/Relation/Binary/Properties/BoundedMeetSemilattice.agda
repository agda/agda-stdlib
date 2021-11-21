------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded meet semilattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.BoundedMeetSemilattice
  {c ℓ₁ ℓ₂} (M : BoundedMeetSemilattice c ℓ₁ ℓ₂) where

open BoundedMeetSemilattice M

open import Algebra.Definitions _≈_
open import Data.Product
open import Function.Base using (_∘_; flip)
open import Relation.Binary
open import Relation.Binary.Properties.Poset poset
import Relation.Binary.Properties.BoundedJoinSemilattice as J

open import Relation.Binary.Lattice.Properties.BoundedMeetSemilattice

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.BoundedMeetSemilattice was deprecated in v2.0.
Use Relation.Binary.Properties.BoundedMeetSemilattice instead."
#-}
