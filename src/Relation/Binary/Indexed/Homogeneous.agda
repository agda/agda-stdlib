------------------------------------------------------------------------
-- The Agda standard library
--
-- Homogeneously-indexed binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Indexed.Homogeneous where

------------------------------------------------------------------------
-- Publicly export core definitions

open import Relation.Binary.Indexed.Homogeneous.Core public
open import Relation.Binary.Indexed.Homogeneous.Definitions public
open import Relation.Binary.Indexed.Homogeneous.Structures public
open import Relation.Binary.Indexed.Homogeneous.Bundles public


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.17

REL = IREL
{-# WARNING_ON_USAGE REL
"Warning: REL was deprecated in v0.17.
Please use IREL instead."
#-}
Rel = IRel
{-# WARNING_ON_USAGE Rel
"Warning: Rel was deprecated in v0.17.
Please use IRel instead."
#-}
