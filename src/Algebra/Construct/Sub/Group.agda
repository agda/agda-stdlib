------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of subgroup via Group monomorphism
--
-- Based on Nathan van Doorn (Taneb)'s original PR
-- https://github.com/agda/agda-stdlib/pull/2852
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group; RawGroup)

module Algebra.Construct.Sub.Group {c ℓ} (G : Group c ℓ) where

open import Algebra.Morphism.Structures using (IsGroupMonomorphism)
open import Algebra.Morphism.GroupMonomorphism using (isGroup)
open import Level using (suc; _⊔_)

private
  module G = Group G

------------------------------------------------------------------------
-- Definition
--
-- Fundamentally, this design is the same as in the above PR:
-- a `SubX` is given by an `X` monomorphism...
-- ... to be able to define such, the current library design requires
-- * *some* `X`-domain of definition for the mono, here given by the
--   placeholder name `domain`, which otherwise plays no role externally
-- * an underlying bare ('raw') function defining the mono, here called
--   (in search of a  canonical name) `ι`, standing for 'injection'
-- * the juice: that `ι` indeed defines a mono from the domain to the
--   (underlying defining `rawX` subfield of the) top-level `X` module parameter

record Subgroup c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field

-- as above, this name is essentially arbitrary,
-- exisitng solely to be mentioned in the third field below

    domain         : RawGroup c′ ℓ′

-- this function (obviously) needs a source and target:
-- * the target, for the sake of the third field, needs to be
--   `Carrier` subfield of the top-level `X` module parameter
-- * the source, however, really exists solely to give a type to `ι`
--   and indeed, the typechecker can infer (from the third field)
--   that this type *must* be the `Carrier` of the `RawX` `domain`

-- Taneb's design introduces a `private` module
-- `private module H = RawGroup domain`
-- for the sake of affording easy/easier named access to its
-- `Carrier` field, and as preferable to the hideous explicit form
-- `RawGroup.Carrier domain` which is the definiens of `H.Carrier`

-- Neither is necessary, but can be, and is, reconstructed by the
-- typechecker by offering instead a placeholder, in exactly the same way
-- that `domain` exists as a named field solely to express the dependency
-- in the type of `ι-monomorphism`. In that sense, it is an ephemeral form
-- derived from `domain`, which moreover will never play a role in client
-- uses of this module, except as a typing constraint on any application
-- of `ι`, a constraint which is already inherited (by definitional equality!)
-- from the type of the `⟦_⟧` parameter to `IsXHomomorphism`...

    ι              : _ → G.Carrier -- where _ = RawGroup.Carrier domain

-- now all the pieces are in place, we can define what we *really* want

    ι-monomorphism : IsGroupMonomorphism domain G.rawGroup ι

-- this is 'admin': any client module of `Subgroup` will likely want to
-- refer to primitive *and* manifest subfields of `IsXMonmorphism`, so
-- this is automatically made available to clients, but not `open`ed,
-- so that such affordance is client-definable, as usual.

  module ι = IsGroupMonomorphism ι-monomorphism

-- Similarly, but mathematically motivated: any client module of `Subgroup`
-- will want access to *the `X` defined as the domain of the `IsXMonomorphism`*.
-- But here, it is both automatically made available to clients, as above,
-- *and* also `open`ed, so that its affordances are offered to any client
-- via the 'canonical' names associated with the `X`/`IsX` bundle/structure

-- Taneb's design does this in two steps:
-- * first, create the `IsX` structure, with name `isX`
-- * second, create the `X` bundle` via `isX`

-- My own thinking on this has evolved: I would rather go straight for the
-- bundle, from which `isX : IsX ...` is definable/exported by `open`.
-- This avoids having to recapitulate the verbose telescope involved in any
-- `IsX <telescope>` (and any design decisions/commitments around such things),
-- or having to choose a name for the `isX` field, when, once again, all the
-- heavy lifting is already made available by the `XHomomorphism` module, so
-- for general DRY reasons, should not be repeated here.

  group : Group _ _
  group = record { isGroup = isGroup ι-monomorphism G.isGroup }

  open Group group public
