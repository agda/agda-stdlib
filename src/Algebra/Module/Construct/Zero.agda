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

module Algebra.Module.Construct.Zero where

open import Algebra.Bundles
open import Algebra.Module.Bundles
open import Data.Unit
open import Level

private
  variable
    r s ℓr ℓs : Level

leftSemimodule : {R : Semiring r ℓr} → LeftSemimodule R 0ℓ 0ℓ
leftSemimodule = record
  { Carrierᴹ = ⊤
  ; _≈ᴹ_ = λ _ _ → ⊤
  }

rightSemimodule : {S : Semiring s ℓs} → RightSemimodule S 0ℓ 0ℓ
rightSemimodule = record
  { Carrierᴹ = ⊤
  ; _≈ᴹ_ = λ _ _ → ⊤
  }

bisemimodule :
  {R : Semiring r ℓr} {S : Semiring s ℓs} → Bisemimodule R S 0ℓ 0ℓ
bisemimodule = record
  { Carrierᴹ = ⊤
  ; _≈ᴹ_ = λ _ _ → ⊤
  }

semimodule : {R : CommutativeSemiring r ℓr} → Semimodule R 0ℓ 0ℓ
semimodule = record
  { Carrierᴹ = ⊤
  ; _≈ᴹ_ = λ _ _ → ⊤
  }

leftModule : {R : Ring r ℓr} → LeftModule R 0ℓ 0ℓ
leftModule = record
  { Carrierᴹ = ⊤
  ; _≈ᴹ_ = λ _ _ → ⊤
  }

rightModule : {S : Ring s ℓs} → RightModule S 0ℓ 0ℓ
rightModule = record
  { Carrierᴹ = ⊤
  ; _≈ᴹ_ = λ _ _ → ⊤
  }

bimodule : {R : Ring r ℓr} {S : Ring s ℓs} → Bimodule R S 0ℓ 0ℓ
bimodule = record
  { Carrierᴹ = ⊤
  ; _≈ᴹ_ = λ _ _ → ⊤
  }

⟨module⟩ : {R : CommutativeRing r ℓr} → Module R 0ℓ 0ℓ
⟨module⟩ = record
  { Carrierᴹ = ⊤
  ; _≈ᴹ_ = λ _ _ → ⊤
  }
