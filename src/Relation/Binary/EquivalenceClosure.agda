------------------------------------------------------------------------
-- The Agda standard library
--
-- Equivalence closures of binary relations
--
-- This module is DEPRECATED. Please use the
-- Relation.Binary.Construct.Closure.Equivalence module directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.EquivalenceClosure where

open import Relation.Binary.Construct.Closure.Equivalence public

{-# WARNING_ON_IMPORT
"Relation.Binary.EquivalenceClosure was deprecated in v0.16.
Use Relation.Binary.Construct.Closure.Equivalence instead."
#-}
