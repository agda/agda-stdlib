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

{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Algebra.Morphism.Construct.Terminal {c ℓ : Level} where

open import Algebra.Bundles.Raw
  using (RawMagma; RawMonoid; RawGroup; RawNearSemiring; RawSemiring; RawRing)
open import Algebra.Morphism.Structures
  using(IsMagmaHomomorphism; IsMonoidHomomorphism; IsGroupHomomorphism
        ; IsNearSemiringHomomorphism; IsSemiringHomomorphism
        ; IsRingHomomorphism)
open import Data.Product.Base using (_,_)
open import Function.Definitions using (StrictlySurjective)
import Relation.Binary.Morphism.Definitions as Rel
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)

open import Algebra.Construct.Terminal {c} {ℓ}

private
  variable
    a ℓa : Level
    A : Set a

------------------------------------------------------------------------
-- The unique morphism

one : A → 𝕆ne.Carrier
one _ = _

------------------------------------------------------------------------
-- Basic properties

strictlySurjective : A → StrictlySurjective 𝕆ne._≈_ one
strictlySurjective x _ = x , _

------------------------------------------------------------------------
-- Homomorphisms

isMagmaHomomorphism : (M : RawMagma a ℓa) →
                      IsMagmaHomomorphism M rawMagma one
isMagmaHomomorphism M = record
  { isRelHomomorphism = record { cong = _ }
  ; homo = _
  }

isMonoidHomomorphism : (M : RawMonoid a ℓa) →
                       IsMonoidHomomorphism M rawMonoid one
isMonoidHomomorphism M = record
  { isMagmaHomomorphism = isMagmaHomomorphism (RawMonoid.rawMagma M)
  ; ε-homo = _
  }

isGroupHomomorphism : (G : RawGroup a ℓa) →
                      IsGroupHomomorphism G rawGroup one
isGroupHomomorphism G = record
  { isMonoidHomomorphism = isMonoidHomomorphism (RawGroup.rawMonoid G)
  ; ⁻¹-homo = λ _ → _
  }

isNearSemiringHomomorphism : (N : RawNearSemiring a ℓa) →
                             IsNearSemiringHomomorphism N rawNearSemiring one
isNearSemiringHomomorphism N = record
  { +-isMonoidHomomorphism = isMonoidHomomorphism (RawNearSemiring.+-rawMonoid N)
  ; *-homo = λ _ _ → _
  }

isSemiringHomomorphism : (S : RawSemiring a ℓa) →
                         IsSemiringHomomorphism S rawSemiring one
isSemiringHomomorphism S = record
  { isNearSemiringHomomorphism = isNearSemiringHomomorphism (RawSemiring.rawNearSemiring S)
  ; 1#-homo = _
  }

isRingHomomorphism : (R : RawRing a ℓa) → IsRingHomomorphism R rawRing one
isRingHomomorphism R = record
  { isSemiringHomomorphism = isSemiringHomomorphism (RawRing.rawSemiring R)
  ; -‿homo = λ _ → _
  }
