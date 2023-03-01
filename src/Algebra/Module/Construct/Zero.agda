------------------------------------------------------------------------
-- The Agda standard library
--
-- This module constructs the zero R-module, and similar for weaker
-- module-like structures.
-- The intended universal property is that, given any R-module M, there
-- is a unique map into and a unique map out of the zero R-module
-- from/to M.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level

module Algebra.Module.Construct.Zero {c ℓ : Level} where

open import Algebra.Bundles
open import Algebra.Module.Bundles
open import Data.Unit.Polymorphic
open import Relation.Binary.Core using (Rel)

private
  variable
    r s ℓr ℓs : Level

------------------------------------------------------------------------
-- gather all the functionality in one place

module ℤero where

  infix  4 _≈ᴹ_
  Carrierᴹ : Set c
  Carrierᴹ = ⊤

  _≈ᴹ_     : Rel Carrierᴹ ℓ
  _ ≈ᴹ _ = ⊤

open ℤero

------------------------------------------------------------------------
-- Raw bundles NOT YET IMPLEMENTED issue #1828
{-
rawModule : RawModule c ℓ
rawModule = record { ℤero }
-}
------------------------------------------------------------------------
-- Bundles

leftSemimodule : {R : Semiring r ℓr} → LeftSemimodule R c ℓ
leftSemimodule = record { ℤero }

rightSemimodule : {S : Semiring s ℓs} → RightSemimodule S c ℓ
rightSemimodule = record { ℤero }

bisemimodule :
  {R : Semiring r ℓr} {S : Semiring s ℓs} → Bisemimodule R S c ℓ
bisemimodule = record { ℤero }

semimodule : {R : CommutativeSemiring r ℓr} → Semimodule R c ℓ
semimodule = record { ℤero }

leftModule : {R : Ring r ℓr} → LeftModule R c ℓ
leftModule = record { ℤero }

rightModule : {S : Ring s ℓs} → RightModule S c ℓ
rightModule = record { ℤero }

bimodule : {R : Ring r ℓr} {S : Ring s ℓs} → Bimodule R S c ℓ
bimodule = record { ℤero }

⟨module⟩ : {R : CommutativeRing r ℓr} → Module R c ℓ
⟨module⟩ = record { ℤero }
