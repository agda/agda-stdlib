------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use the
-- Relation.Binary.Construct.Closure.Reflexive module directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.ReflexiveClosure where

open import Relation.Binary.Construct.Closure.Reflexive public

{-# WARNING_ON_IMPORT
"Data.ReflexiveClosure was deprecated in v0.16.
Use Relation.Binary.Construct.Closure.Reflexive instead."
#-}
