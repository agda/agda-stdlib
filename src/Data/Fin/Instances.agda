------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for finite sets
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Instances where

open import Data.Fin.Base
open import Data.Fin.Properties

instance
  Fin-≡-isDecEquivalence = ≡-isDecEquivalence
  Fin-≤-isDecTotalOrder = ≤-isDecTotalOrder
