------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneously-indexed binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Indexed.Heterogeneous where

------------------------------------------------------------------------
-- Publicly export core definitions

open import Relation.Binary.Indexed.Heterogeneous.Core public
open import Relation.Binary.Indexed.Heterogeneous.Definitions public
open import Relation.Binary.Indexed.Heterogeneous.Structures public
open import Relation.Binary.Indexed.Heterogeneous.Bundles public


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
Setoid = IndexedSetoid
{-# WARNING_ON_USAGE Setoid
"Warning: Setoid was deprecated in v0.17.
Please use IndexedSetoid instead."
#-}
IsEquivalence = IsIndexedEquivalence
{-# WARNING_ON_USAGE IsEquivalence
"Warning: IsEquivalence was deprecated in v0.17.
Please use IsIndexedEquivalence instead."
#-}
