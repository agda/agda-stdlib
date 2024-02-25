------------------------------------------------------------------------
-- The Agda standard library
--
-- The unique morphism to the terminal object,
-- for each of the relevant categories. Since
-- each terminal algebra builds on `Monoid`,
-- possibly with additional (trivial) operations,
-- satisfying additional properties, it suffices to
-- define the morphism on the underlying `RawMonoid`
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (Level)

module Algebra.Morphism.Construct.Terminal {c ℓ : Level} where


open import Algebra.Bundles.Raw
  using (RawMonoid; RawGroup; RawNearSemiring; RawSemiring; RawRing)
import Algebra.Morphism.Definitions as MorphismDefinitions
open import Algebra.Morphism.Structures
  using ( module MagmaMorphisms
        ; module MonoidMorphisms
        ; module GroupMorphisms
        ; module NearSemiringMorphisms
        ; module SemiringMorphisms
        ; module RingWithoutOneMorphisms
        ; module RingMorphisms
        )
open import Data.Product.Base using (_,_)
open import Function.Definitions using (StrictlySurjective)
import Relation.Binary.Morphism.Definitions as Definitions
open import Relation.Binary.Morphism.Structures

open import Algebra.Construct.Terminal {c} {ℓ}

private
  variable
    a ℓa : Level


------------------------------------------------------------------------
-- The underlying data of the morphism

module UniqueMorphism (M : RawMonoid a ℓa) where

  private module M = RawMonoid M
  open MorphismDefinitions M.Carrier 𝕆ne.Carrier 𝕆ne._≈_
  open MagmaMorphisms M.rawMagma rawMagma

  one : M.Carrier → 𝕆ne.Carrier
  one _ = _

  cong : Definitions.Homomorphic₂ M.Carrier 𝕆ne.Carrier M._≈_ 𝕆ne._≈_ one
  cong _ = _

  isRelHomomorphism : IsRelHomomorphism M._≈_ 𝕆ne._≈_ one
  isRelHomomorphism = record { cong = cong }

  homo : Homomorphic₂ one M._∙_ _
  homo _ = _

  ε-homo : Homomorphic₀ one M.ε _
  ε-homo = _

  isMagmaHomomorphism : IsMagmaHomomorphism one
  isMagmaHomomorphism = record
    { isRelHomomorphism = isRelHomomorphism
    ; homo = homo
    }

  strictlySurjective : StrictlySurjective 𝕆ne._≈_ one
  strictlySurjective _ = M.ε , _

------------------------------------------------------------------------
-- Monoid

module _ (M : RawMonoid a ℓa) where

  open MonoidMorphisms M rawMonoid
  open UniqueMorphism M

  isMonoidHomomorphism : IsMonoidHomomorphism one
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = isMagmaHomomorphism
    ; ε-homo = ε-homo
    }

------------------------------------------------------------------------
-- Group

module _ (G : RawGroup a ℓa) where

  private module G = RawGroup G
  open GroupMorphisms G rawGroup
  open UniqueMorphism G.rawMonoid

  isGroupHomomorphism : IsGroupHomomorphism one
  isGroupHomomorphism = record
    { isMonoidHomomorphism = isMonoidHomomorphism G.rawMonoid
    ; ⁻¹-homo = λ _ → _
    }

------------------------------------------------------------------------
-- NearSemiring

module _ (N : RawNearSemiring a ℓa) where

  private module N = RawNearSemiring N
  open NearSemiringMorphisms N rawNearSemiring
  open UniqueMorphism N.+-rawMonoid

  isNearSemiringHomomorphism : IsNearSemiringHomomorphism one
  isNearSemiringHomomorphism = record
    { +-isMonoidHomomorphism = isMonoidHomomorphism N.+-rawMonoid
    ; *-homo = λ _ _ → _
    }

------------------------------------------------------------------------
-- Semiring

module _ (S : RawSemiring a ℓa) where

  private module S = RawSemiring S
  open SemiringMorphisms S rawSemiring
  open UniqueMorphism S.+-rawMonoid

  isSemiringHomomorphism : IsSemiringHomomorphism one
  isSemiringHomomorphism = record
    { isNearSemiringHomomorphism = isNearSemiringHomomorphism S.rawNearSemiring
    ; 1#-homo = _
    }

------------------------------------------------------------------------
-- Ring

module _ (R : RawRing a ℓa) where

  private module R = RawRing R
  open RingMorphisms R rawRing
  open UniqueMorphism R.+-rawMonoid

  isRingHomomorphism : IsRingHomomorphism one
  isRingHomomorphism = record
    { isSemiringHomomorphism = isSemiringHomomorphism R.rawSemiring
    ; -‿homo = λ _ → _
    }
