------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of normal subgroups
--
-- Based on Nathan van Doorn (Taneb)'s original PR
-- https://github.com/agda/agda-stdlib/pull/2852
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group)

-- This module relocates Taneb's original `Algebra.NormalSubgroup`
-- to a level one *below* that of `Algebra.Construct.Sub.Group`,
-- for the 'obvious' inheritance hierarchy 'reason' that a
-- `NormalSubgroup` is a specialisation of the notion of `Subgroup`.

-- `Normal` as a root name avoids recapitulation of the parent name
-- `Subgroup`, but also permits/does not frustrate development of a
-- companion `Construct` sub-hierarchy (intersections etc.) below
-- `Algebra/Construct/Sub/Group/Normal` as a sub-directory.

module Algebra.Construct.Sub.Group.Normal {c ℓ} (G : Group c ℓ)  where

open import Algebra.Construct.Sub.Group G using (Subgroup)
open import Function.Base using (typeOf)
open import Level using (suc; _⊔_)

private
  module G = Group G

------------------------------------------------------------------------
-- Definition
--
-- IsNormal: every element of the given subgroup commutes in the parent.
--
-- This defined as a `record`, as usual in order to improve type inference,
-- specifically that a `NormalSubgroup` below may (usually) be definable
-- solely by supplying its `isNormal` field.

record IsNormal {c′ ℓ′} (subgroup : Subgroup c′ ℓ′) : Set (c ⊔ ℓ ⊔ c′) where

-- A design question here is how much of the `Subgroup` structure should/must
-- be exposed in the course of defining the fields here.

-- Surely we need the name of the function which witnesses 'subX'-ness,
-- but not the property `ι-isXMonomorphism`.

  open Subgroup subgroup using (ι)

  field

-- But it's not obvious that we need the (name of) `Carrier` of the `domain`
-- of the `Subgroup`, viz. the source of `ι`, except as the type of variables
-- quantifed here as `n` (as generic name for 'element's of the normal subgroup).

-- As with `Subgroup` itself, this domain `Carrier` type is canonically inferrable
-- by the typechecker, as in the inline comment. But perhaps this use of `_` might
-- also be usefully documented as `Function.Base.typeOf n`?

    conjugate : ∀ n g → _ -- where _ = RawGroup.Carrier (Subgroup.domain subgroup)

-- The main field of interest only requires that the `conjugate` field be
-- of type 'source of `ι`'; but we don't need that type here, otherwise the
-- `∀ n` quantifier would need an explicit type label, and such inferrability
-- reinforces the decision nowhere to name this type.

    normal : ∀ n g → ι (conjugate n g) G.∙ g G.≈ g G.∙ ι n

-- NormalSubgroup: a Subgroup which IsNormal (sic)

record NormalSubgroup c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field
    subgroup : Subgroup c′ ℓ′
    isNormal : IsNormal subgroup

-- But again, and for generic `library-design` reasons, we publicaly export
-- all the subfields of each field, in order to afford a standardised vocabulary
-- for all the structure intended to be in scope when using a `NormalSubgroup`.

-- Locally, we have used only name `ι` in the definition of `IsNormal`,
-- but clients may also want access ot the full signature (eg. esp. the
-- `ι-isGroupMonomorphism` field which characterises being a subgroup).

  open Subgroup subgroup public
  open IsNormal isNormal public
