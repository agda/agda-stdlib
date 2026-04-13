------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for signs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sign.Instances where

open import Data.Sign.Properties

instance
  Sign-≡-isDecEquivalence = ≡-isDecEquivalence
