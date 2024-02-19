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

open import Algebra.Bundles using (Magma)
open import Algebra.Bundles.Raw using (RawMagma)
open import Algebra.Construct.Initial {c} {ℓ}
import Algebra.Morphism.Definitions as MorphismDefinitions
open import Algebra.Morphism.Structures using (module MagmaMorphisms)
open import Function.Definitions using (Injective)
import Relation.Binary.Morphism.Definitions as Definitions
open import Relation.Binary.Morphism.Structures

private
  variable
    m ℓm : Level


------------------------------------------------------------------------
-- The underlying data of the morphism

module UniqueMorphism (M : RawMagma m ℓm) where

  open RawMagma M
  open MorphismDefinitions ℤero.Carrier Carrier _≈_

  zero : ℤero.Carrier → Carrier
  zero ()

  cong : Definitions.Homomorphic₂ ℤero.Carrier Carrier ℤero._≈_ _≈_ zero
  cong {x = ()}

  isRelHomomorphism : IsRelHomomorphism ℤero._≈_ _≈_ zero
  isRelHomomorphism = record { cong = cong }

  homo : Homomorphic₂ zero ℤero._∙_ _∙_
  homo ()

  injective : Injective ℤero._≈_ _≈_ zero
  injective {x = ()}

------------------------------------------------------------------------
-- Magma

module _ (M : Magma m ℓm) where

  private module M = Magma M
  open MagmaMorphisms rawMagma M.rawMagma
  open UniqueMorphism M.rawMagma

  isMagmaHomomorphism : IsMagmaHomomorphism zero
  isMagmaHomomorphism = record
    { isRelHomomorphism = isRelHomomorphism
    ; homo = homo
    }

  isMagmaMonomorphism : IsMagmaMonomorphism zero
  isMagmaMonomorphism = record
    { isMagmaHomomorphism = isMagmaHomomorphism
    ; injective = injective
    }
