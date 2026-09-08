------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of algebraic structures where the carrier is ⊤. In
-- mathematics, this is usually called 0 (1 in the case of Monoid, Group).
--
-- From monoids up, these are zero-objects – i.e, both the initial
-- and the terminal object in the relevant category.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Algebra.Construct.Terminal {c ℓ : Level} where

open import Algebra.Bundles
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Binary.Core using (Rel)

------------------------------------------------------------------------
-- Gather all the functionality in one place

module 𝕆ne where

  infix  4 _≈_
  Carrier : Set c
  Carrier = ⊤

  _≈_   : Rel Carrier ℓ
  _ ≈ _ = ⊤

------------------------------------------------------------------------
-- Raw bundles

rawMagma : RawMagma c ℓ
rawMagma = record { 𝕆ne }

rawMonoid : RawMonoid c ℓ
rawMonoid = record { 𝕆ne }

rawGroup : RawGroup c ℓ
rawGroup = record { 𝕆ne }

rawNearSemiring : RawNearSemiring c ℓ
rawNearSemiring = record { 𝕆ne }

rawSemiring : RawSemiring c ℓ
rawSemiring = record { 𝕆ne }

rawRing : RawRing c ℓ
rawRing = record { 𝕆ne }

------------------------------------------------------------------------
-- Bundles

magma : Magma c ℓ
magma = record { 𝕆ne }

semigroup : Semigroup c ℓ
semigroup = record { 𝕆ne }

band : Band c ℓ
band = record { 𝕆ne }

commutativeSemigroup : CommutativeSemigroup c ℓ
commutativeSemigroup = record { 𝕆ne }

monoid : Monoid c ℓ
monoid = record { 𝕆ne }

commutativeMonoid : CommutativeMonoid c ℓ
commutativeMonoid = record { 𝕆ne }

idempotentCommutativeMonoid : IdempotentCommutativeMonoid c ℓ
idempotentCommutativeMonoid = record { 𝕆ne }

group : Group c ℓ
group = record { 𝕆ne }

abelianGroup : AbelianGroup c ℓ
abelianGroup = record { 𝕆ne }

nearSemiring : NearSemiring c ℓ
nearSemiring = record { 𝕆ne }

semiring : Semiring c ℓ
semiring = record { 𝕆ne }

ring : Ring c ℓ
ring = record { 𝕆ne }

