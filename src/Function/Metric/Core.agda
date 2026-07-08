------------------------------------------------------------------------
-- The Agda standard library
--
-- Core metric definitions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Metric.Core where

open import Level using (Level)
private
  variable
    a i : Level

------------------------------------------------------------------------
-- Distance functions

DistanceFunction : Set a → Set i → Set _
DistanceFunction A I = A → A → I
