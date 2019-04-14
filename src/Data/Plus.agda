------------------------------------------------------------------------
-- The Agda standard library
--
-- Transitive closures
--
-- This module is DEPRECATED. Please use the
-- Relation.Binary.Construct.Closure.Transitive module directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Plus where

open import Relation.Binary.Construct.Closure.Transitive public

{-# WARNING_ON_IMPORT
"Data.Plus was deprecated in v0.16.
Use Relation.Binary.Construct.Closure.Transitive instead."
#-}
