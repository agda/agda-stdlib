------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of algebraic lattice structures where the carrier is ⊤.
-- In mathematics, this is usually called 0.
--
-- From monoids up, these are are zero-objects – i.e, both the initial
-- and the terminal object in the relevant category.
-- For structures without an identity element, we can't necessarily
-- produce a homomorphism out of 0, because there is an instance of such
-- a structure with an empty Carrier.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (Level)

module Algebra.Lattice.Construct.Zero {c ℓ : Level} where

open import Algebra.Lattice.Bundles
open import Data.Unit.Polymorphic

------------------------------------------------------------------------
-- Bundles

semilattice : Semilattice c ℓ
semilattice = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }
