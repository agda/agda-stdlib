------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for bits
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Instances where

open import Data.Bin.Properties

instance
  ≡-isDecEquivalence-Bin = ≡-isDecEquivalence
