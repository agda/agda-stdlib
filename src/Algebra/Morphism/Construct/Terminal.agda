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

open import Algebra.Bundles using (Monoid; Group; NearSemiring; Semiring; Ring)
open import Algebra.Bundles.Raw using (RawMonoid; RawGroup)
open import Algebra.Construct.Terminal {c} {ℓ}
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

private
  variable
    a ℓa : Level


------------------------------------------------------------------------
-- The underlying data of the morphism

module TheMorphism (M : RawMonoid a ℓa) where

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

module _ (M : Monoid a ℓa) where

  private module M = Monoid M
  open MonoidMorphisms M.rawMonoid rawMonoid
  open TheMorphism M.rawMonoid

  isMonoidHomomorphism : IsMonoidHomomorphism one
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = isMagmaHomomorphism
    ; ε-homo = ε-homo
    }

------------------------------------------------------------------------
-- Group

module _ (G : Group a ℓa) where

  private module G = Group G
  open GroupMorphisms G.rawGroup rawGroup
  open TheMorphism G.rawMonoid

  isGroupHomomorphism : IsGroupHomomorphism one
  isGroupHomomorphism = record
    { isMonoidHomomorphism = isMonoidHomomorphism G.monoid
    ; ⁻¹-homo = λ _ → _
    }

------------------------------------------------------------------------
-- NearSemiring

module _ (N : NearSemiring a ℓa) where

  private module N = NearSemiring N
  open NearSemiringMorphisms N.rawNearSemiring rawNearSemiring
  open TheMorphism N.+-rawMonoid

  isNearSemiringHomomorphism : IsNearSemiringHomomorphism one
  isNearSemiringHomomorphism = record
    { +-isMonoidHomomorphism = isMonoidHomomorphism N.+-monoid
    ; *-homo = λ _ _ → _
    }

------------------------------------------------------------------------
-- Semiring

module _ (S : Semiring a ℓa) where

  private module S = Semiring S
  open SemiringMorphisms S.rawSemiring rawSemiring
  open TheMorphism S.+-rawMonoid

  isSemiringHomomorphism : IsSemiringHomomorphism one
  isSemiringHomomorphism = record
    { isNearSemiringHomomorphism = isNearSemiringHomomorphism S.nearSemiring
    ; 1#-homo = _
    }

------------------------------------------------------------------------
-- Ring

module _ (R : Ring a ℓa) where

  private module R = Ring R
  open RingMorphisms R.rawRing rawRing
  open TheMorphism R.+-rawMonoid
  isRingHomomorphism : IsRingHomomorphism one
  isRingHomomorphism = record
    { isSemiringHomomorphism = isSemiringHomomorphism R.semiring
    ; -‿homo = λ _ → _
    }
