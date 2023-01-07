------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of algebraic structures where the carrier is ⊤.
-- In mathematics, this is usually called 0 (1 in the case of Group).
--
-- From monoids up, these are zero-objects – i.e, both the initial
-- and the terminal object in the relevant category.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Algebra.Construct.Terminal {c ℓ : Level} where

open import Algebra.Bundles
open import Data.Unit.Polymorphic
open import Relation.Binary.Core using (Rel)

------------------------------------------------------------------------
-- gather all the functionality in one place

private module 𝕆ne where

  infix  4 _≈_
  Carrier : Set c
  _≈_     : Rel Carrier ℓ

  Carrier = ⊤
  _ ≈ _ = ⊤

open 𝕆ne

------------------------------------------------------------------------
-- Raw bundles

rawMagma : RawMagma c ℓ
rawMagma = record { Carrier = Carrier ; _≈_ = _≈_ }

rawMonoid : RawMonoid c ℓ
rawMonoid = record { Carrier = Carrier ; _≈_ = _≈_ }

rawGroup : RawGroup c ℓ
rawGroup = record { Carrier = Carrier ; _≈_ = _≈_ }

rawSemiring : RawSemiring c ℓ
rawSemiring = record { Carrier = Carrier ; _≈_ = _≈_ }

rawRing : RawRing c ℓ
rawRing = record { Carrier = Carrier ; _≈_ = _≈_ }

------------------------------------------------------------------------
-- Bundles

magma : Magma c ℓ
magma = record { Carrier = Carrier ; _≈_ = _≈_ }

semigroup : Semigroup c ℓ
semigroup = record { Carrier = Carrier ; _≈_ = _≈_ }

band : Band c ℓ
band = record { Carrier = Carrier ; _≈_ = _≈_ }

commutativeSemigroup : CommutativeSemigroup c ℓ
commutativeSemigroup = record { Carrier = Carrier ; _≈_ = _≈_ }

monoid : Monoid c ℓ
monoid = record { Carrier = Carrier ; _≈_ = _≈_ }

commutativeMonoid : CommutativeMonoid c ℓ
commutativeMonoid = record { Carrier = Carrier ; _≈_ = _≈_ }

idempotentCommutativeMonoid : IdempotentCommutativeMonoid c ℓ
idempotentCommutativeMonoid = record { Carrier = Carrier ; _≈_ = _≈_ }

group : Group c ℓ
group = record { Carrier = Carrier ; _≈_ = _≈_ }

abelianGroup : AbelianGroup c ℓ
abelianGroup = record { Carrier = Carrier ; _≈_ = _≈_ }

semiring : Semiring c ℓ
semiring = record { Carrier = Carrier ; _≈_ = _≈_ }

ring : Ring c ℓ
ring = record { Carrier = Carrier ; _≈_ = _≈_ }

