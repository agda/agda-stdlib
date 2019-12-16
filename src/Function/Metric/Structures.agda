------------------------------------------------------------------------
-- The Agda standard library
--
-- Some metric structures (not packed up with sets, operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should usually be accessed via
-- `Function.Metric`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary hiding (Symmetric)

module Function.Metric.Structures
  {a i ℓ₁ ℓ₂ ℓ₃} {A : Set a} {I : Set i}
  (_≈ₐ_ : Rel A ℓ₁) (_≈ᵢ_ : Rel I ℓ₂) (_≤_ : Rel I ℓ₃) (0# : I) where

open import Algebra.FunctionProperties using (Op₂)
open import Function.Metric.Core
open import Function.Metric.Definitions
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Proto-metrics

record IsProtoMetric (d : DistanceFunction A I)
                   : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isTotalOrder     : IsTotalOrder _≈ᵢ_ _≤_
    ≈-isEquivalence  : IsEquivalence _≈ₐ_
    cong             : Congruent _≈ₐ_ _≈ᵢ_ d
    positive         : ∀ {x y} → 0# ≤ d x y

  open IsTotalOrder isTotalOrder public
    renaming (module Eq to ImageEq)

  module CarrierEq = IsEquivalence ≈-isEquivalence

------------------------------------------------------------------------
-- Pre-metrics

record IsPreMetric (d : DistanceFunction A I)
                 : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isProtoMetric : IsProtoMetric d
    eq⇒0          : PositiveDefinite _≈ₐ_ _≈ᵢ_ d 0#

  open IsProtoMetric isProtoMetric public

------------------------------------------------------------------------
-- Quasi-semi-metrics

record IsQuasiSemiMetric (d : DistanceFunction A I)
                       : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isPreMetric      : IsPreMetric d
    0⇒eq             : ∀ {x y} → d x y ≈ᵢ 0# → x ≈ₐ y

  open IsPreMetric isPreMetric public

------------------------------------------------------------------------
-- Semi-metrics

record IsSemiMetric (d : DistanceFunction A I)
                  : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isQuasiSemiMetric : IsQuasiSemiMetric d
    sym               : Symmetric _≈ᵢ_ d

  open IsQuasiSemiMetric isQuasiSemiMetric public

------------------------------------------------------------------------
-- General metrics

-- A general metric obeys a generalised form of the triangle inequality.
-- It can be specialised to a standard metric/ultrametric/inframetric etc.
-- by providing the correct operator.

record IsGeneralMetric (_∙_ : Op₂ I) (d : DistanceFunction A I)
                     : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isSemiMetric : IsSemiMetric d
    triangle     : TriangleInequality _≤_ _∙_ d

  open IsSemiMetric isSemiMetric public
