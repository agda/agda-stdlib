------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of left modules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles        using (Ring)
open import Algebra.Module.Bundles using (LeftModule)
open import Level                  using (Level)

module Algebra.Module.Properties.LeftModule
  {r ℓr m ℓm : Level}
  {ring  : Ring r ℓr}
  (mod   : LeftModule ring m ℓm)
  where

open Ring       ring
open LeftModule mod
open import Algebra.Properties.AbelianGroup +ᴹ-abelianGroup public
  using ()
  renaming (inverseˡ-unique to inverseˡ-uniqueᴹ
           ; inverseʳ-unique to inverseʳ-uniqueᴹ
           ; ⁻¹-involutive to -ᴹ-involutive)
