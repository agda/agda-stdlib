------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of sub-bimodules
--
-- This is based on Nathan van Doorn (Taneb)'s PR
-- https://github.com/agda/agda-stdlib/pull/2852
-- but uses the `Algebra.Construct.Sub.AbelianGroup` module
-- to plumb in that any sub-bimodule of a `Bimodule` defines
-- a sub-AbelianGroup, hence a `NormalSubgroup`, so that when
-- an ideal in a `Ring` is defined as a suitable sub-bimodule,
-- the quotient structure of the additive subgroup is immediate,
-- on which the quotient `Ring` structure may then be defined.
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

-- As with `Algebra.Construct.Sub.Group{.Normal}`, we refrain from explicit
-- naming of the source type of the underlying function. In terms of the
-- `RawBimodule` signature, this is `Carrierᴹ`, which will also be,
-- definitionally, the `Carrier` of the associated `(Abelian)Group` sub-bundle
-- defined by `ι.+ᴹ-isGroupMonomorphism` below.

    ι              : _ → M.Carrierᴹ -- where _ = RawBimodule.Carrierᴹ domain

    ι-monomorphism : IsBimoduleMonomorphism domain M.rawBimodule ι

-- As with `Algebra.Construct.Sub.Group`, we create a module out of the
-- `IsBimoduleMonomorphism` field, allowing us to expose its rich derived
-- substructures, here specifically, the `+ᴹ-isGroupMonomorphism` definition.

  module ι = IsBimoduleMonomorphism ι-monomorphism

  bimodule : Bimodule R S _ _
  bimodule = record
    { isBimodule = isBimodule ι-monomorphism R.isRing S.isRing M.isBimodule }

  open Bimodule bimodule public

-- Additionally, have Abelian (hence: Normal) subgroups of M.+ᴹ-abelianGroup

  subgroup : Subgroup cm′ ℓm′
  subgroup = record { ι-monomorphism = ι.+ᴹ-isGroupMonomorphism }

-- Exporting these two fields, but *without* their types, allows us to
-- avoid explicit import of `Algebra.Construct.Sub.Group.Normal`, in
-- favour of their encapsulation in `Algebra.Construct.Sub.AbelianGroup`.

-- isNormal : Algebra.Construct.Sub.Group.Normal.IsNormal M.+ᴹ-group subgroup
  isNormal = AbelianSubgroup.isNormal subgroup

-- normalSubgroup : Algebra.Construct.Sub.Group.Normal.NormalSubgroup M.+ᴹ-group _ _
  normalSubgroup = AbelianSubgroup.normalSubgroup subgroup
