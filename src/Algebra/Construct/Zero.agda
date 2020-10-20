------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of algebraic structures where the carrier is ⊤.
-- In mathematics, this is usually called 0.
--
-- From monoids up, these are are zero-objects – i.e, both the initial
-- and the terminal object in the relevant category.
-- For structures without an identity element, we can't necessarily
-- produce a homomorphism out of 0, because there is an instance of such
-- a structure with an empty Carrier.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Algebra.Construct.Zero {ℓ : Level} where

open import Algebra.Bundles
open import Data.Unit.Polymorphic

------------------------------------------------------------------------
-- Raw bundles

rawMagma : RawMagma ℓ ℓ
rawMagma = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

rawMonoid : RawMonoid ℓ ℓ
rawMonoid = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

rawGroup : RawGroup ℓ ℓ
rawGroup = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

------------------------------------------------------------------------
-- Bundles

magma : Magma ℓ ℓ
magma = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

semigroup : Semigroup ℓ ℓ
semigroup = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

band : Band ℓ ℓ
band = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

commutativeSemigroup : CommutativeSemigroup ℓ ℓ
commutativeSemigroup = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

semilattice : Semilattice ℓ ℓ
semilattice = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

monoid : Monoid ℓ ℓ
monoid = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

commutativeMonoid : CommutativeMonoid ℓ ℓ
commutativeMonoid = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

idempotentCommutativeMonoid : IdempotentCommutativeMonoid ℓ ℓ
idempotentCommutativeMonoid = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

group : Group ℓ ℓ
group = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

abelianGroup : AbelianGroup ℓ ℓ
abelianGroup = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }
