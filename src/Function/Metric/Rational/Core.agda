------------------------------------------------------------------------
-- The Agda standard library
--
-- Core definitions for metrics over ℕ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Rational.Base using (ℚ)
import Function.Metric.Core as Base

module Function.Metric.Rational.Core where

------------------------------------------------------------------------
-- Definition

DistanceFunction : ∀ {a} → Set a → Set a
DistanceFunction A = Base.DistanceFunction A ℚ
