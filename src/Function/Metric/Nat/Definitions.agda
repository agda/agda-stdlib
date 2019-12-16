------------------------------------------------------------------------
-- The Agda standard library
--
-- Core definitions for metrics over ℕ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Metric.Nat.Definitions where

open import Algebra.Core using (Op₂)
open import Data.Nat.Base
open import Level using (Level)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

open import Function.Metric.Nat.Core
import Function.Metric.Definitions as Base

private
  variable
    a ℓ : Level
    A   : Set a

------------------------------------------------------------------------
-- Properties

-- Basic

Congruent : Rel A ℓ → DistanceFunction A → Set _
Congruent _≈ₐ_ d = Base.Congruent _≈ₐ_ _≡_ d

Symmetric : DistanceFunction A → Set _
Symmetric = Base.Symmetric _≡_

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

-- Other

Bounded : DistanceFunction A → Set _
Bounded = Base.Bounded _≤_

TranslationInvariant : Op₂ A → DistanceFunction A → Set _
TranslationInvariant = Base.TranslationInvariant _≡_
