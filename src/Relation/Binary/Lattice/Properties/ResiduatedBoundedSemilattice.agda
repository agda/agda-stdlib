------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of residuated bounded semilattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Ordered.Residuated using (ResiduatedBoundedSemilattice)

module Relation.Binary.Lattice.Properties.ResiduatedBoundedSemilattice
  {a ℓ₁ ℓ₂} (rbsl : ResiduatedBoundedSemilattice a ℓ₁ ℓ₂)
  where

open ResiduatedBoundedSemilattice rbsl

open import Algebra.Definitions _≈_ using (LeftZero; RightZero; Zero)
open import Algebra.Ordered.Structures using (IsPosemiring)
open import Algebra.Ordered.Bundles using (Posemiring)
import Algebra.Properties.RightResiduatedPomonoid as RightResiduatedPomonoid
open import Data.Product using (_,_)
open import Function.GaloisConnection using (GaloisConnection)
open import Relation.Binary.Lattice.Properties.BoundedJoinSemilattice
  boundedJoinSemilattice using (isCommutativePomonoid)
open import Relation.Binary.Lattice.Properties.ResiduatedSemilattice
  residuatedSemilattice using (∙-∨-distrib)

open RightResiduatedPomonoid leftResiduatedPomonoid using ()
  renaming (galoisConnection to ∙-//-galoisConnection)
open RightResiduatedPomonoid rightResiduatedPomonoid using ()
  renaming (galoisConnection to ∙-\\-galoisConnection)

-- Every residuated bounded lattice induces an (idempotent) posemiring.

zeroˡ : LeftZero ⊥ _∙_
zeroˡ x = ⊥-pres minimum minimum
  where open GaloisConnection (∙-//-galoisConnection x)

zeroʳ : RightZero ⊥ _∙_
zeroʳ x = ⊥-pres minimum minimum
  where open GaloisConnection (∙-\\-galoisConnection x)

zero : Zero ⊥ _∙_
zero = zeroˡ , zeroʳ

isPosemiring : IsPosemiring _≈_ _≤_ _∨_ _∙_ ⊥ ε
isPosemiring = record
  { +-isCommutativePomonoid = isCommutativePomonoid
  ; *-mono                  = ∙-mono
  ; *-assoc                 = assoc
  ; *-identity              = identity
  ; distrib                 = ∙-∨-distrib
  ; zero                    = zero
  }

posemiring : Posemiring a ℓ₁ ℓ₂
posemiring = record { isPosemiring = isPosemiring }
