------------------------------------------------------------------------
-- The Agda standard library
--
-- Core definitions for metrics over ℚ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Rational.Base
open import Function using (const)
open import Level using (Level; suc)
open import Relation.Binary hiding (Symmetric)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Function.Metric.Rational.Core
open import Function.Metric.Rational.Definitions
import Function.Metric.Structures as Base

module Function.Metric.Rational.Structures where

private
  variable
    a ℓ : Level
    A   : Set a

------------------------------------------------------------------------
-- Proto-metrics

IsProtoMetric : Rel A ℓ → DistanceFunction A → Set _
IsProtoMetric _≈_ = Base.IsProtoMetric _≈_ _≡_ _≤_ 0ℚ

open Base using (module IsProtoMetric) public

------------------------------------------------------------------------
-- Pre-metrics

IsPreMetric : Rel A ℓ → DistanceFunction A → Set _
IsPreMetric _≈_ = Base.IsPreMetric _≈_ _≡_ _≤_ 0ℚ

open Base using (module IsPreMetric) public

------------------------------------------------------------------------
-- Quasi-semi-metrics

IsQuasiSemiMetric : Rel A ℓ → DistanceFunction A → Set _
IsQuasiSemiMetric _≈_ = Base.IsQuasiSemiMetric _≈_ _≡_ _≤_ 0ℚ

open Base using (module IsQuasiSemiMetric) public

------------------------------------------------------------------------
-- Semi-metrics

IsSemiMetric : Rel A ℓ → DistanceFunction A → Set _
IsSemiMetric _≈_ = Base.IsSemiMetric _≈_ _≡_ _≤_ 0ℚ

open Base using (module IsSemiMetric) public

------------------------------------------------------------------------
-- Metrics

IsMetric : Rel A ℓ → DistanceFunction A → Set _
IsMetric _≈_ = Base.IsGeneralMetric _≈_ _≡_ _≤_ 0ℚ _+_

module IsMetric {_≈_ : Rel A ℓ} {d : DistanceFunction A}
                (M : IsMetric _≈_ d) where
  open Base.IsGeneralMetric M public

------------------------------------------------------------------------
-- Ultra-metrics

IsUltraMetric : Rel A ℓ → DistanceFunction A → Set _
IsUltraMetric _≈_ = Base.IsGeneralMetric _≈_ _≡_ _≤_ 0ℚ _⊔_

module IsUltraMetric {_≈_ : Rel A ℓ} {d : DistanceFunction A}
                     (UM : IsUltraMetric _≈_ d) where
  open Base.IsGeneralMetric UM public
