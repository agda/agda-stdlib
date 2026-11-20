------------------------------------------------------------------------
-- The Agda standard library
--
-- This is a stub: Properties satisfied by Boolean Algebra
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice.Bundles using (BooleanAlgebra)

module Relation.Binary.Lattice.Properties.BooleanAlgebra
  {c ℓ₁ ℓ₂} (L : BooleanAlgebra c ℓ₁ ℓ₂) where

open BooleanAlgebra L

------------------------------------------------------------------------
-- Re-export: BooleanAlgebras are HeytingAlgebras

open import Relation.Binary.Lattice.Properties.HeytingAlgebra heytingAlgebra public
