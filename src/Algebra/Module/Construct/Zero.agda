------------------------------------------------------------------------
-- The Agda standard library
--
-- This module constructs the zero R-module, and similar for weaker
-- module-like structures.
-- The intended universal property is that, given any R-module M, there
-- is a unique map into and a unique map out of the zero R-module
-- from/to M.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

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

private module ℤero where

  infix  4 _≈_
  Carrier : Set c
  Carrier = ⊤

  _≈_     : Rel Carrier ℓ
  _ ≈ _ = ⊤

open ℤero

------------------------------------------------------------------------
-- Raw bundles NOT YET IMPLEMENTED issue #1828
{-
rawModule : RawModule c ℓ
rawModule = record { Carrier = Carrier ; _≈_ = _≈_ }
-}
------------------------------------------------------------------------
-- Bundles

leftSemimodule : {R : Semiring r ℓr} → LeftSemimodule R c ℓ
leftSemimodule = record { Carrierᴹ = Carrier ; _≈ᴹ_ = _≈_ }

rightSemimodule : {S : Semiring s ℓs} → RightSemimodule S c ℓ
rightSemimodule = record { Carrierᴹ = Carrier ; _≈ᴹ_ = _≈_ }

bisemimodule :
  {R : Semiring r ℓr} {S : Semiring s ℓs} → Bisemimodule R S c ℓ
bisemimodule = record { Carrierᴹ = Carrier ; _≈ᴹ_ = _≈_ }

semimodule : {R : CommutativeSemiring r ℓr} → Semimodule R c ℓ
semimodule = record { Carrierᴹ = Carrier ; _≈ᴹ_ = _≈_ }

leftModule : {R : Ring r ℓr} → LeftModule R c ℓ
leftModule = record { Carrierᴹ = Carrier ; _≈ᴹ_ = _≈_ }

rightModule : {S : Ring s ℓs} → RightModule S c ℓ
rightModule = record { Carrierᴹ = Carrier ; _≈ᴹ_ = _≈_ }

bimodule : {R : Ring r ℓr} {S : Ring s ℓs} → Bimodule R S c ℓ
bimodule = record { Carrierᴹ = Carrier ; _≈ᴹ_ = _≈_ }

⟨module⟩ : {R : CommutativeRing r ℓr} → Module R c ℓ
⟨module⟩ = record { Carrierᴹ = Carrier ; _≈ᴹ_ = _≈_ }
