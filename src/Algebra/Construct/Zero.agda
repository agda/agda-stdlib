------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of algebraic structures where the carrier is ⊤.
-- In mathematics, this is usually called 0.
--
-- From monoids up, these are are zero-objects – i.e, both the initial
-- and the terminal object in the relevant category.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Construct.Zero where

open import Algebra
open import Data.Unit
open import Level using (Level; 0ℓ)

rawMagma : RawMagma 0ℓ 0ℓ
rawMagma = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

magma : Magma 0ℓ 0ℓ
magma = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

semigroup : Semigroup 0ℓ 0ℓ
semigroup = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

band : Band 0ℓ 0ℓ
band = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
commutativeSemigroup = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

semilattice : Semilattice 0ℓ 0ℓ
semilattice = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

rawMonoid : RawMonoid 0ℓ 0ℓ
rawMonoid = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

monoid : Monoid 0ℓ 0ℓ
monoid = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
commutativeMonoid = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

idempotentCommutativeMonoid : IdempotentCommutativeMonoid 0ℓ 0ℓ
idempotentCommutativeMonoid = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

rawGroup : RawGroup 0ℓ 0ℓ
rawGroup = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

group : Group 0ℓ 0ℓ
group = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

abelianGroup : AbelianGroup 0ℓ 0ℓ
abelianGroup = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }
