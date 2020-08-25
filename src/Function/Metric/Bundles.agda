------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for metrics
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Function.Metric`.

{-# OPTIONS --without-K --safe #-}

module Function.Metric.Bundles  where

open import Algebra.Core using (Op₂)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Core using (Rel)

open import Function.Metric.Structures
open import Function.Metric.Core

------------------------------------------------------------------------
-- ProtoMetric

record ProtoMetric (a i ℓ₁ ℓ₂ ℓ₃ : Level)
                 : Set (suc (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Carrier       : Set a
    Image         : Set i
    _≈_           : Rel Carrier ℓ₁
    _≈ᵢ_          : Rel Image ℓ₂
    _≤_           : Rel Image ℓ₃
    0#            : Image
    d             : DistanceFunction Carrier Image
    isProtoMetric : IsProtoMetric _≈_ _≈ᵢ_ _≤_ 0# d

  open IsProtoMetric isProtoMetric public

------------------------------------------------------------------------
-- PreMetric

record PreMetric (a i ℓ₁ ℓ₂ ℓ₃ : Level)
               : Set (suc (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Carrier     : Set a
    Image       : Set i
    _≈_         : Rel Carrier ℓ₁
    _≈ᵢ_        : Rel Image ℓ₂
    _≤_         : Rel Image ℓ₃
    0#          : Image
    d           : DistanceFunction Carrier Image
    isPreMetric : IsPreMetric _≈_ _≈ᵢ_ _≤_ 0# d

  open IsPreMetric isPreMetric public

  protoMetric : ProtoMetric a i ℓ₁ ℓ₂ ℓ₃
  protoMetric = record
    { isProtoMetric = isProtoMetric
    }

------------------------------------------------------------------------
-- QuasiSemiMetric

record QuasiSemiMetric (a i ℓ₁ ℓ₂ ℓ₃ : Level)
                     : Set (suc (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Carrier           : Set a
    Image             : Set i
    _≈_               : Rel Carrier ℓ₁
    _≈ᵢ_              : Rel Image ℓ₂
    _≤_               : Rel Image ℓ₃
    0#                : Image
    d                 : DistanceFunction Carrier Image
    isQuasiSemiMetric : IsQuasiSemiMetric _≈_ _≈ᵢ_ _≤_ 0# d

  open IsQuasiSemiMetric isQuasiSemiMetric public

  preMetric : PreMetric a i ℓ₁ ℓ₂ ℓ₃
  preMetric = record
    { isPreMetric = isPreMetric
    }

  open PreMetric preMetric public
    using (protoMetric)

------------------------------------------------------------------------
-- SemiMetric

record SemiMetric (a i ℓ₁ ℓ₂ ℓ₃ : Level)
                : Set (suc (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Carrier      : Set a
    Image        : Set i
    _≈_          : Rel Carrier ℓ₁
    _≈ᵢ_         : Rel Image ℓ₂
    _≤_          : Rel Image ℓ₃
    0#           : Image
    d            : DistanceFunction Carrier Image
    isSemiMetric : IsSemiMetric _≈_ _≈ᵢ_ _≤_ 0# d

  open IsSemiMetric isSemiMetric public

  quasiSemiMetric : QuasiSemiMetric a i ℓ₁ ℓ₂ ℓ₃
  quasiSemiMetric = record
    { isQuasiSemiMetric = isQuasiSemiMetric
    }

  open QuasiSemiMetric quasiSemiMetric public
    using (protoMetric; preMetric)

------------------------------------------------------------------------
-- GeneralMetric

-- Note that this package is not necessarily a metric in the classical
-- sense as there is no way to ensure that the _∙_ operator really
-- represents addition. See `Function.Metric.Nat` and
-- `Function.Metric.Rational` for more specialised `Metric` and
-- `UltraMetric` packages.

-- See the discussion accompanying the `IsGeneralMetric` structure for
-- more details.

record GeneralMetric (a i ℓ₁ ℓ₂ ℓ₃ : Level)
                   : Set (suc (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Carrier         : Set a
    Image           : Set i
    _≈_             : Rel Carrier ℓ₁
    _≈ᵢ_            : Rel Image ℓ₂
    _≤_             : Rel Image ℓ₃
    0#              : Image
    _∙_             : Op₂ Image
    d               : DistanceFunction Carrier Image
    isGeneralMetric : IsGeneralMetric _≈_ _≈ᵢ_ _≤_ 0# _∙_ d

  open IsGeneralMetric isGeneralMetric public

  semiMetric : SemiMetric a i ℓ₁ ℓ₂ ℓ₃
  semiMetric = record
    { isSemiMetric = isSemiMetric
    }

  open SemiMetric semiMetric public
    using (protoMetric; preMetric; quasiSemiMetric)
