------------------------------------------------------------------------
-- The Agda standard library
--
-- Refinement type: a value together with a proof irrelevant witness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Refinement where

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Refinement.Base public

------------------------------------------------------------------------
-- Publicly re-export queries

open import Data.Refinement.Properties public
  using (value-injective; _≟_)
