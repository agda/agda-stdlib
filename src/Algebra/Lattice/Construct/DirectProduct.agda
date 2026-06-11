------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of algebraic structures made by taking two other instances
-- A and B, and having elements of the new instance be pairs |A| × |B|.
-- In mathematics, this would usually be written A × B or A ⊕ B.
--
-- From semigroups up, these new instances are products of the relevant
-- category. For structures with commutative addition (commutative
-- monoids, Abelian groups, semirings, rings), the direct product is
-- also the coproduct, making it a biproduct.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Lattice.Construct.DirectProduct where

open import Algebra using (Band)
open import Algebra.Lattice using (Semilattice)
import Algebra.Construct.DirectProduct as DirectProduct
open import Data.Product.Base using (_,_; _<*>_)
open import Level using (Level; _⊔_)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Bundles

semilattice : Semilattice a ℓ₁ → Semilattice b ℓ₂ →
              Semilattice (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
semilattice L M = record
  { isSemilattice = record
    { isBand = Band.isBand (DirectProduct.band L.band M.band)
    ; comm   = λ x y → (L.comm , M.comm) <*> x <*> y
    }
  } where module L = Semilattice L; module M = Semilattice M
