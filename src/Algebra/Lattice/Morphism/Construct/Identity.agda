------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity morphism for algebraic lattice structures
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Algebra.Lattice.Morphism.Construct.Identity where

open import Algebra.Lattice.Bundles
open import Algebra.Lattice.Morphism.Structures
  using ( module LatticeMorphisms )
open import Data.Product.Base using (_,_)
open import Function.Base using (id)
open import Level using (Level)
open import Relation.Binary.Morphism.Construct.Identity using (isRelHomomorphism)
open import Relation.Binary.Definitions using (Reflexive)

private
  variable
    c ℓ : Level

module _ (L : RawLattice c ℓ) (open RawLattice L) (refl : Reflexive _≈_) where
  open LatticeMorphisms L L

  isLatticeHomomorphism : IsLatticeHomomorphism id
  isLatticeHomomorphism = record
    { isRelHomomorphism = isRelHomomorphism _
    ; ∧-homo            = λ _ _ → refl
    ; ∨-homo            = λ _ _ → refl
    }

  isLatticeMonomorphism : IsLatticeMonomorphism id
  isLatticeMonomorphism = record
    { isLatticeHomomorphism = isLatticeHomomorphism
    ; injective = id
    }

  isLatticeIsomorphism : IsLatticeIsomorphism id
  isLatticeIsomorphism = record
    { isLatticeMonomorphism = isLatticeMonomorphism
    ; surjective = _, refl
    }
