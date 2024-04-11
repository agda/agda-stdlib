------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for metrics over ℚ
------------------------------------------------------------------------

-- Unfortunately, unlike definitions and structures, the bundles over
-- general metric spaces cannot be reused as it is impossible to
-- constrain the image set to ℚ.

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Metric.Rational.Bundles where

open import Function.Base using (const)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)

open import Function.Metric.Rational.Core using (DistanceFunction)
open import Function.Metric.Rational.Structures
open import Function.Metric.Bundles as Base
  using (GeneralMetric)

------------------------------------------------------------------------
-- Proto-metric

record ProtoMetric a ℓ : Set (suc (a ⊔ ℓ)) where
  field
    Carrier       : Set a
    _≈_           : Rel Carrier ℓ
    d             : DistanceFunction Carrier
    isProtoMetric : IsProtoMetric _≈_ d

  infix 4 _≈_

  open IsProtoMetric isProtoMetric public

------------------------------------------------------------------------
-- PreMetric

record PreMetric a ℓ : Set (suc (a ⊔ ℓ)) where
  field
    Carrier     : Set a
    _≈_         : Rel Carrier ℓ
    d           : DistanceFunction Carrier
    isPreMetric : IsPreMetric _≈_ d

  infix 4 _≈_

  open IsPreMetric isPreMetric public

  protoMetric : ProtoMetric a ℓ
  protoMetric = record
    { isProtoMetric = isProtoMetric
    }

------------------------------------------------------------------------
-- QuasiSemiMetric

record QuasiSemiMetric a ℓ : Set (suc (a ⊔ ℓ)) where
  field
    Carrier           : Set a
    _≈_               : Rel Carrier ℓ
    d                 : DistanceFunction Carrier
    isQuasiSemiMetric : IsQuasiSemiMetric _≈_ d

  infix 4 _≈_

  open IsQuasiSemiMetric isQuasiSemiMetric public

  preMetric : PreMetric a ℓ
  preMetric = record
    { isPreMetric = isPreMetric
    }

  open PreMetric preMetric public
    using (protoMetric)

------------------------------------------------------------------------
-- SemiMetric

record SemiMetric a ℓ : Set (suc (a ⊔ ℓ)) where
  field
    Carrier      : Set a
    _≈_          : Rel Carrier ℓ
    d            : DistanceFunction Carrier
    isSemiMetric : IsSemiMetric _≈_ d

  infix 4 _≈_

  open IsSemiMetric isSemiMetric public

  quasiSemiMetric : QuasiSemiMetric a ℓ
  quasiSemiMetric = record
    { isQuasiSemiMetric = isQuasiSemiMetric
    }

  open QuasiSemiMetric quasiSemiMetric public
    using (protoMetric; preMetric)

------------------------------------------------------------------------
-- Metrics

record Metric a ℓ : Set (suc (a ⊔ ℓ)) where
  field
    Carrier  : Set a
    _≈_      : Rel Carrier ℓ
    d        : DistanceFunction Carrier
    isMetric : IsMetric _≈_ d

  infix 4 _≈_

  open IsMetric isMetric public

  semiMetric : SemiMetric a ℓ
  semiMetric = record
    { isSemiMetric = isSemiMetric
    }

  open SemiMetric semiMetric public
    using (protoMetric; preMetric; quasiSemiMetric)

------------------------------------------------------------------------
-- UltraMetrics

record UltraMetric a ℓ : Set (suc (a ⊔ ℓ)) where
  field
    Carrier       : Set a
    _≈_           : Rel Carrier ℓ
    d             : DistanceFunction Carrier
    isUltraMetric : IsUltraMetric _≈_ d

  infix 4 _≈_

  open IsUltraMetric isUltraMetric public

  semiMetric : SemiMetric a ℓ
  semiMetric = record
    { isSemiMetric = isSemiMetric
    }

  open SemiMetric semiMetric public
    using (protoMetric; preMetric; quasiSemiMetric)
