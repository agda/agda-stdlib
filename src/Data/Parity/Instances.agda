------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for parities
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Parity.Instances where

open import Data.Parity.Properties

instance
  Parity-≡-isDecEquivalence = ≡-isDecEquivalence
