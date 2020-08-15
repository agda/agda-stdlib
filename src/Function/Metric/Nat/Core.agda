------------------------------------------------------------------------
-- The Agda standard library
--
-- Core definitions for metrics over ℕ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Metric.Nat.Core where

open import Data.Nat.Base using (ℕ)
import Function.Metric.Core as Base

------------------------------------------------------------------------
-- Definition

DistanceFunction : ∀ {a} → Set a → Set a
DistanceFunction A = Base.DistanceFunction A ℕ
