------------------------------------------------------------------------
-- The Agda standard library
--
-- The unique morphism from the initial object,
-- for each of the relevant categories. Since
-- `Semigroup` and `Band` are simply `Magma`s
-- satisfying additional properties, it suffices to
-- define the morphism on the underlying `RawMagma`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (Level)

module Algebra.Morphism.Construct.Initial {c ℓ : Level} where

open import Algebra.Bundles.Raw using (RawMagma)
open import Algebra.Morphism.Structures
open import Function.Definitions using (Injective)
import Relation.Binary.Morphism.Definitions as Rel
open import Relation.Binary.Morphism.Structures
open import Relation.Binary.Core using (Rel)

open import Algebra.Construct.Initial {c} {ℓ}

private
  variable
    a m ℓm : Level
    A : Set a
    ≈ : Rel A ℓm

------------------------------------------------------------------------
-- The unique morphism

zero : ℤero.Carrier → A
zero ()

------------------------------------------------------------------------
-- Basic properties

cong : (≈ : Rel A ℓm) → Rel.Homomorphic₂ ℤero.Carrier A ℤero._≈_ ≈ zero
cong _ {x = ()}

injective : (≈ : Rel A ℓm) → Injective ℤero._≈_ ≈ zero
injective _ {x = ()}

------------------------------------------------------------------------
-- Morphism structures

isMagmaHomomorphism : (M : RawMagma m ℓm) →
                      IsMagmaHomomorphism rawMagma M zero
isMagmaHomomorphism M = record
  { isRelHomomorphism = record { cong = cong (RawMagma._≈_ M) }
  ; homo = λ()
  }

isMagmaMonomorphism : (M : RawMagma m ℓm) →
                      IsMagmaMonomorphism rawMagma M zero
isMagmaMonomorphism M = record
  { isMagmaHomomorphism = isMagmaHomomorphism M
  ; injective = injective (RawMagma._≈_ M)
  }
