------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of algebraic structures where the carrier is ⊤.
-- In mathematics, this is usually called 0 (1 in the case of Group).
--
-- From monoids up, these are are zero-objects – i.e, both the initial
-- and the terminal object in the relevant category.
--
-- For structures without an identity element, the terminal algebra is
-- *not*  initial, because there is an instance of such a structure
-- with an empty Carrier. Accordingly, such definitions are now deprecated
-- in favour of those defined in `Algebra.Construct.Terminal`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (Level)

module Algebra.Construct.Zero {c ℓ : Level} where

open import Algebra.Bundles.Raw
  using (RawMagma)
open import Algebra.Bundles
  using (Magma; Semigroup; Band)

------------------------------------------------------------------------
-- Re-export those algebras which are both initial and terminal

open import Algebra.Construct.Terminal public
  hiding (rawMagma; magma; semigroup; band)

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new definitions re-exported from
-- `Algebra.Construct.Terminal` as continuing support for the below is
-- not guaranteed.

-- Version 2.0

rawMagma : RawMagma c ℓ
rawMagma = Algebra.Construct.Terminal.rawMagma

{-# WARNING_ON_USAGE rawMagma
"Warning: rawMagma was deprecated in v2.0.
Please use Algebra.Construct.Terminal.rawMagma instead."
#-}

magma : Magma c ℓ
magma = Algebra.Construct.Terminal.magma
{-# WARNING_ON_USAGE magma
"Warning: magma was deprecated in v2.0.
Please use Algebra.Construct.Terminal.magma instead."
#-}

semigroup : Semigroup c ℓ
semigroup = Algebra.Construct.Terminal.semigroup
{-# WARNING_ON_USAGE semigroup
"Warning: semigroup was deprecated in v2.0.
Please use Algebra.Construct.Terminal.semigroup instead."
#-}

band : Band c ℓ
band = Algebra.Construct.Terminal.band
{-# WARNING_ON_USAGE semigroup
"Warning: semigroup was deprecated in v2.0.
Please use Algebra.Construct.Terminal.semigroup instead."
#-}
