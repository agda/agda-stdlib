------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char.Instances where

open import Data.Char.Properties using (isDecEquivalence)

instance
  Char-≡-isDecEquivalence = isDecEquivalence
