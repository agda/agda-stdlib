------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for parities
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Parity.Instances where

open import Data.Parity.Properties

instance
  Parity-≡-isDecEquivalence = ≡-isDecEquivalence
