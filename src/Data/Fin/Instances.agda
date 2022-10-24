------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for finite sets
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Instances where

open import Data.Fin.Base
open import Data.Fin.Properties

instance
  Fin-≡-isDecEquivalence = ≡-isDecEquivalence
  Fin-≤-isDecTotalOrder = ≤-isDecTotalOrder
