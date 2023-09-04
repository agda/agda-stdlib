------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of modules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra                using (CommutativeRing; Involutive)
open import Algebra.Module.Bundles using (Module)
open import Level                  using (Level)

module Algebra.Module.Properties
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (mod       : Module ring m ℓm)
  where

open Module mod
open import Algebra.Module.Properties.Semimodule semimodule public
open import Algebra.Properties.Group using (⁻¹-involutive)

-ᴹ-involutive : Involutive _≈ᴹ_ -ᴹ_
-ᴹ-involutive = ⁻¹-involutive +ᴹ-group
