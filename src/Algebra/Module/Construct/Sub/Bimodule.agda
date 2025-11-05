------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of sub-bimodules
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Ring)
open import Algebra.Module.Bundles using (Bimodule; RawBimodule)

module Algebra.Module.Construct.Sub.Bimodule
  {cr ℓr cs ℓs cm ℓm} {R : Ring cr ℓr} {S : Ring cs ℓs}  (M : Bimodule R S cm ℓm)
  where

open import Algebra.Module.Morphism.Structures using (IsBimoduleMonomorphism)
open import Algebra.Module.Morphism.BimoduleMonomorphism using (isBimodule)
open import Level using (suc; _⊔_)

private
  module R = Ring R
  module S = Ring S
  module M = Bimodule M

open import Algebra.Construct.Sub.AbelianGroup M.+ᴹ-abelianGroup
  as AbelianSubgroup
  using (Subgroup)

------------------------------------------------------------------------
-- Definition

record Subbimodule cm′ ℓm′ : Set (cr ⊔ cs ⊔ cm ⊔ ℓm ⊔ suc (cm′ ⊔ ℓm′)) where
  field
    domain         : RawBimodule R.Carrier S.Carrier cm′ ℓm′
    ι              : _ → M.Carrierᴹ
    ι-monomorphism : IsBimoduleMonomorphism domain M.rawBimodule ι

  module ι = IsBimoduleMonomorphism ι-monomorphism

  bimodule : Bimodule R S _ _
  bimodule = record
    { isBimodule = isBimodule ι-monomorphism R.isRing S.isRing M.isBimodule }

  open Bimodule bimodule public

-- Additionally, have Abelian (hence: Normal) subgroups of M.+ᴹ-abelianGroup

  subgroup : Subgroup cm′ ℓm′
  subgroup = record { ι-monomorphism = ι.+ᴹ-isGroupMonomorphism }

  isNormal = AbelianSubgroup.isNormal subgroup

  normalSubgroup = AbelianSubgroup.normalSubgroup subgroup
