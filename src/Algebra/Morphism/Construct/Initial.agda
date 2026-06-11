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
  using (IsMagmaHomomorphism; IsMagmaMonomorphism)
open import Function.Definitions using (Congruent; Injective)
open import Relation.Binary.Core using (Rel)

open import Algebra.Construct.Initial {c} {ℓ}

private
  variable
    a m ℓm : Level
    A : Set a


------------------------------------------------------------------------
-- The unique morphism

zero : ℤero.Carrier → A
zero ()

------------------------------------------------------------------------
-- Basic properties

module _ (≈ : Rel A ℓm) where

  cong : Congruent ℤero._≈_ ≈ zero
  cong {x = ()}

  injective : Injective ℤero._≈_ ≈ zero
  injective {x = ()}

------------------------------------------------------------------------
-- Morphism structures

module _ (M : RawMagma m ℓm) where

  open RawMagma M using (_≈_)

  isMagmaHomomorphism : IsMagmaHomomorphism rawMagma M zero
  isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = cong _≈_ }
    ; homo = λ()
    }

  isMagmaMonomorphism : IsMagmaMonomorphism rawMagma M zero
  isMagmaMonomorphism = record
    { isMagmaHomomorphism = isMagmaHomomorphism
    ; injective = injective _≈_
    }
