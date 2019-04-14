------------------------------------------------------------------------
-- The Agda standard library
--
-- The reflexive transitive closures of McBride, Norell and Jansson
--
-- This module is DEPRECATED. Please use the
-- Relation.Binary.Construct.Closure.ReflexiveTransitive module directly
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Star where

open import Relation.Binary.Construct.Closure.ReflexiveTransitive public

{-# WARNING_ON_IMPORT
"Data.Star was deprecated in v0.16.
Use Relation.Binary.Construct.Closure.ReflexiveTransitive instead."
#-}
