------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for metrics over ℕ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Metric.Nat.Bundles where

open import Data.Nat.Base hiding (suc)
open import Function using (const)
open import Level using (Level; 0ℓ; suc) renaming (_⊔_ to _⊔ₗ_)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
  using (_≡_; isEquivalence)

open import Function.Metric.Nat.Core
open import Function.Metric.Nat.Structures
open import Function.Metric.Bundles as Base
  using (GeneralMetric)

------------------------------------------------------------------------
-- Many of the simpler packages are simply re-exported

open Base public using
  ( ProtoMetric
  ; PreMetric
  ; QuasiSemiMetric
  ; SemiMetric
  )

------------------------------------------------------------------------
-- Metrics

record Metric a ℓ : Set (suc (a ⊔ₗ ℓ)) where
  field
    Carrier  : Set a
    _≈_      : Rel Carrier ℓ
    d        : DistanceFunction Carrier
    isMetric : IsMetric _≈_ d

  open IsMetric isMetric public

  generalMetric : GeneralMetric a 0ℓ ℓ 0ℓ 0ℓ
  generalMetric = record
    { isGeneralMetric = isMetric
    }

  open GeneralMetric generalMetric public
    using
    ( protoMetric; preMetric
    ; quasiSemiMetric; semiMetric
    )

------------------------------------------------------------------------
-- UltraMetrics

record UltraMetric a ℓ : Set (suc (a ⊔ₗ ℓ)) where
  field
    Carrier       : Set a
    _≈_           : Rel Carrier ℓ
    d             : DistanceFunction Carrier
    isUltraMetric : IsUltraMetric _≈_ d

  open IsUltraMetric isUltraMetric public

  generalMetric : GeneralMetric a 0ℓ ℓ 0ℓ 0ℓ
  generalMetric = record
    { isGeneralMetric = isUltraMetric
    }

  open GeneralMetric generalMetric public
    using
    ( protoMetric; preMetric
    ; quasiSemiMetric; semiMetric
    )
