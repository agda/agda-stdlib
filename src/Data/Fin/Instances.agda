------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for finite sets
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Instances where

open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (≡-isDecEquivalence; ≤-isDecTotalOrder)

instance
  Fin-≡-isDecEquivalence = ≡-isDecEquivalence
  Fin-≤-isDecTotalOrder = ≤-isDecTotalOrder
