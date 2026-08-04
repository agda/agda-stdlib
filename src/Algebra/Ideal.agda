------------------------------------------------------------------------
-- The Agda standard library
--
-- Ideals of a ring
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles

module Algebra.Ideal {c ℓ} (R : Ring c ℓ) where

open Ring R

open import Algebra.Module.Bundles.Raw
import Algebra.Module.Construct.TensorUnit as TU
open import Algebra.Module.Morphism.Structures
open import Algebra.NormalSubgroup (+-group)
open import Data.Product.Base
open import Level
open import Relation.Binary.Reasoning.Setoid setoid

record Ideal c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field
    I : RawModule Carrier c′ ℓ′
    ι : RawModule.Carrierᴹ I → Carrier
    ι-monomorphism : IsModuleMonomorphism I (TU.rawModule {R = rawRing}) ι

  module I = RawModule I
  module ι = IsModuleMonomorphism ι-monomorphism

  normalSubgroup : NormalSubgroup c′ ℓ′
  normalSubgroup = record
    { N = I.+ᴹ-rawGroup
    ; ι = ι
    ; ι-monomorphism = ι.+ᴹ-isGroupMonomorphism
    ; normal = λ n g → record
      { fst = n
      -- this ends up a lot simpler now
      ; snd = +-comm g (ι n)
      }
    }
