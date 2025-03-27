------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of right modules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles        using (Ring)
open import Algebra.Module.Bundles using (RightModule)
open import Level                  using (Level)

module Algebra.Module.Properties.RightModule
  {r ℓr m ℓm : Level}
  {ring  : Ring r ℓr}
  (mod   : RightModule ring m ℓm)
  where

open Ring        ring
open RightModule mod
open import Algebra.Properties.AbelianGroup +ᴹ-abelianGroup public
  using ()
  renaming (inverseˡ-unique to inverseˡ-uniqueᴹ
           ; inverseʳ-unique to inverseʳ-uniqueᴹ
           ; ⁻¹-involutive to -ᴹ-involutive)
