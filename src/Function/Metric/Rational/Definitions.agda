------------------------------------------------------------------------
-- The Agda standard library
--
-- Core definitions for metrics over ℚ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core using (Op₂)
open import Data.Rational.Base
open import Level using (Level)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

open import Function.Metric.Rational.Core
import Function.Metric.Definitions as Base

module Function.Metric.Rational.Definitions where

private
  variable
    a ℓ : Level
    A   : Set a

------------------------------------------------------------------------
-- Properties

-- Basic

Congruent : Rel A ℓ → DistanceFunction A → Set _
Congruent _≈ₐ_ d = Base.Congruent _≈ₐ_ _≡_ d

Indiscernable : Rel A ℓ → DistanceFunction A → Set _
Indiscernable _≈ₐ_ d = Base.Indiscernable _≈ₐ_ _≡_ d 0ℚ

Definite : Rel A ℓ → DistanceFunction A → Set _
Definite _≈ₐ_ d = Base.Definite _≈ₐ_ _≡_ d 0ℚ

Symmetric : DistanceFunction A → Set _
Symmetric = Base.Symmetric _≡_

Bounded : DistanceFunction A → Set _
Bounded = Base.Bounded _≤_

TranslationInvariant : Op₂ A → DistanceFunction A → Set _
TranslationInvariant = Base.TranslationInvariant _≡_

-- Inequalities

TriangleInequality : DistanceFunction A → Set _
TriangleInequality = Base.TriangleInequality _≤_ _+_

MaxTriangleInequality : DistanceFunction A → Set _
MaxTriangleInequality = Base.TriangleInequality _≤_ _⊔_

-- Contractions

Contracting : (A → A) → DistanceFunction A → Set _
Contracting = Base.Contracting _≤_

ContractingOnOrbits : (A → A) → DistanceFunction A → Set _
ContractingOnOrbits = Base.ContractingOnOrbits _≤_

StrictlyContracting : Rel A ℓ → (A → A) → DistanceFunction A → Set _
StrictlyContracting _≈_ = Base.StrictlyContracting _≈_ _<_

StrictlyContractingOnOrbits : Rel A ℓ → (A → A) → DistanceFunction A → Set _
StrictlyContractingOnOrbits _≈_ = Base.StrictlyContractingOnOrbits _≈_ _<_
