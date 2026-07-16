------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic structure of functional vectors
--
-- These are essentially 'free' because everything lifts pointwise
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional.Algebra.Base where

open import Algebra.Bundles using (Magma; Semigroup; Band; CommutativeSemigroup;
  Monoid; CommutativeMonoid; Group; AbelianGroup; NearSemiring; SemiringWithoutOne;
  CommutativeSemiringWithoutOne; Semiring; CommutativeSemiring; IdempotentSemiring;
  KleeneAlgebra; Quasiring; Ring; CommutativeRing)
import Algebra.Construct.Pointwise as Lift
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Functional
open import Level using (Level; _⊔_)

private
  variable
    a c ℓ : Level

-- only build the Bundles as the structure can be extracted from them
module _ (n : ℕ) where
  magma : Magma a ℓ → Magma a ℓ
  magma = Lift.magma (Fin n)

  semigroup : Semigroup a ℓ → Semigroup a ℓ
  semigroup = Lift.semigroup (Fin n)

  band : Band a ℓ → Band a ℓ
  band = Lift.band (Fin n)

  commutativeSemigroup : CommutativeSemigroup a ℓ → CommutativeSemigroup a ℓ
  commutativeSemigroup = Lift.commutativeSemigroup (Fin n)

  monoid : Monoid a ℓ → Monoid a ℓ
  monoid = Lift.monoid (Fin n)

  commutativeMonoid : CommutativeMonoid a ℓ → CommutativeMonoid a ℓ
  commutativeMonoid = Lift.commutativeMonoid (Fin n)

  group : Group a ℓ → Group a ℓ
  group = Lift.group (Fin n)

  abelianGroup : AbelianGroup a ℓ → AbelianGroup a ℓ
  abelianGroup = Lift.abelianGroup (Fin n)

  nearSemiring : NearSemiring a ℓ → NearSemiring a ℓ
  nearSemiring = Lift.nearSemiring (Fin n)

  semiringWithoutOne : SemiringWithoutOne a ℓ → SemiringWithoutOne a ℓ
  semiringWithoutOne = Lift.semiringWithoutOne (Fin n)

  commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne a ℓ → CommutativeSemiringWithoutOne a ℓ
  commutativeSemiringWithoutOne = Lift.commutativeSemiringWithoutOne (Fin n)

  semiring : Semiring a ℓ → Semiring a ℓ
  semiring = Lift.semiring (Fin n)

  commutativeSemiring : CommutativeSemiring a ℓ → CommutativeSemiring a ℓ
  commutativeSemiring = Lift.commutativeSemiring (Fin n)

  idempotentSemiring : IdempotentSemiring a ℓ → IdempotentSemiring a ℓ
  idempotentSemiring = Lift.idempotentSemiring (Fin n)

  kleeneAlgebra : KleeneAlgebra a ℓ → KleeneAlgebra a ℓ
  kleeneAlgebra = Lift.kleeneAlgebra (Fin n)

  quasiring : Quasiring a ℓ → Quasiring a ℓ
  quasiring = Lift.quasiring (Fin n)

  ring : Ring a ℓ → Ring a ℓ
  ring = Lift.ring (Fin n)

  commutativeRing : CommutativeRing a ℓ → CommutativeRing a ℓ
  commutativeRing = Lift.commutativeRing (Fin n)
