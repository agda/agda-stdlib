------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of bimodules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles        using (Ring)
open import Algebra.Module.Bundles using (Bimodule)
open import Level                  using (Level)

module Algebra.Module.Properties.Bimodule
  {r ℓr s ℓs m ℓm : Level}
  {ringR : Ring r ℓr} {ringS : Ring s ℓs}
  (mod   : Bimodule ringR ringS m ℓm)
  where

open Bimodule mod
open import Algebra.Module.Properties.LeftModule leftModule public
  using (inverseˡ-uniqueᴹ; inverseʳ-uniqueᴹ; -ᴹ-involutive)
