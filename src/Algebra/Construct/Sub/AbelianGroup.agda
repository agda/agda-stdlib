------------------------------------------------------------------------
-- The Agda standard library
--
-- Subgroups of Abelian groups: necessarily Normal
--
-- This is a strict addition/extension to Nathan van Doorn (Taneb)'s PR
-- https://github.com/agda/agda-stdlib/pull/2852
-- and avoids the lemma `Algebra.NormalSubgroup.abelian⇒subgroup-normal`
-- introduced in PR https://github.com/agda/agda-stdlib/pull/2854
-- in favour of the direct definition of the field `normal` below.
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (AbelianGroup)

module Algebra.Construct.Sub.AbelianGroup {c ℓ} (G : AbelianGroup c ℓ) where

-- As with the corresponding appeal to `IsGroup` in the module
-- `Algebra.Construct.Sub.AbelianGroup`, this import drives the export
-- of the `X` bundle corresponding to the `subX` structure/bundle
-- being defined here.

open import Algebra.Morphism.GroupMonomorphism using (isAbelianGroup)

private
  module G = AbelianGroup G

-- Here, we could chose simply to expose the `NormalSubgroup` definition
-- from `Algebra.Construct.Sub.Group.Normal`, but as this module will use
-- type inference to allow the creation of `NormalSubgroup`s based on their
-- `isNormal` fields alone, it makes sense also to export the type `IsNormal`.

open import Algebra.Construct.Sub.Group.Normal G.group
  using (IsNormal; NormalSubgroup)

-- Re-export the notion of subgroup of the underlying Group

open import Algebra.Construct.Sub.Group G.group public
  using (Subgroup)

-- Then, for any such Subgroup:
-- * it is, in fact, Normal
-- * and defines an AbelianGroup, not just a Group

module _ {c′ ℓ′} (subgroup : Subgroup c′ ℓ′) where

-- Here, we do need both the underlying function `ι` of the mono, and
-- the proof `ι-monomorphism`, in order to be able to construct an
-- `IsAbelianGroup` structure on the way to the `AbelianGroup` bundle.

  open Subgroup subgroup public
    using (ι; ι-monomorphism)

-- Here, we eta-contract the use of `G.comm` in defining the `normal` field.

  isNormal : IsNormal subgroup
  isNormal = record { normal = λ n → G.comm (ι n) }

-- And the use of `record`s throughout permits this 'boilerplate' construction.

  normalSubgroup : NormalSubgroup c′ ℓ′
  normalSubgroup = record { isNormal = isNormal }

-- And the `public` re-export of its substructure.

  open NormalSubgroup normalSubgroup public
    using (conjugate; normal)

-- As with `Algebra.Construct.Sub.Group`, there seems no need to create
-- an intermediate manifest field `isAbelianGroup`, when this may be, and
-- is, obtained by opening the bundle for `public` export.

  abelianGroup : AbelianGroup c′ ℓ′
  abelianGroup = record
    { isAbelianGroup = isAbelianGroup ι-monomorphism G.isAbelianGroup }

  open AbelianGroup abelianGroup public
