------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of properties over distance functions
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Function.Metric`.

{-# OPTIONS --without-K --safe #-}

module Function.Metric.Definitions where

open import Algebra.Core using (Op₂)
open import Data.Product using (∃)
open import Function.Metric.Core using (DistanceFunction)
open import Level using (Level)
open import Relation.Binary.Core using (Rel; _Preserves₂_⟶_⟶_)
open import Relation.Nullary using (¬_)

private
  variable
    a i ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    I : Set i

-----------------------------------------------------------------------
-- Properties

Congruent : Rel A ℓ₁ → Rel I ℓ₂ → DistanceFunction A I → Set _
Congruent _≈ₐ_ _≈ᵢ_ d = d Preserves₂ _≈ₐ_ ⟶ _≈ₐ_ ⟶ _≈ᵢ_

Indiscernable : Rel A ℓ₁ → Rel I ℓ₂ → DistanceFunction A I → I → Set _
Indiscernable _≈ₐ_ _≈ᵢ_ d 0# = ∀ {x y} → d x y ≈ᵢ 0# → x ≈ₐ y

Definite : Rel A ℓ₁ → Rel I ℓ₂ → DistanceFunction A I → I → Set _
Definite _≈ₐ_ _≈ᵢ_ d 0# = ∀ {x y} → x ≈ₐ y → d x y ≈ᵢ 0#

NonNegative : Rel I ℓ₂ → DistanceFunction A I → I → Set _
NonNegative _≤_ d 0# = ∀ {x y} → 0# ≤ d x y

Symmetric : Rel I ℓ → DistanceFunction A I → Set _
Symmetric _≈_ d = ∀ x y → d x y ≈ d y x

TriangleInequality : Rel I ℓ → Op₂ I → DistanceFunction A I → _
TriangleInequality _≤_ _∙_ d = ∀ x y z → d x z ≤ (d x y ∙ d y z)

Bounded : Rel I ℓ → DistanceFunction A I → Set _
Bounded _≤_ d = ∃ λ n → ∀ x y → d x y ≤ n

TranslationInvariant : Rel I ℓ₂ → Op₂ A → DistanceFunction A I → Set _
TranslationInvariant _≈_ _∙_ d = ∀ {x y a} → d (x ∙ a) (y ∙ a) ≈ d x y

Contracting : Rel I ℓ → (A → A) → DistanceFunction A I → Set _
Contracting _≤_ f d = ∀ x y → d (f x) (f y) ≤ d x y

ContractingOnOrbits : Rel I ℓ → (A → A) → DistanceFunction A I → Set _
ContractingOnOrbits _≤_ f d = ∀ x → d (f x) (f (f x)) ≤ d x (f x)

StrictlyContracting : Rel A ℓ₁ → Rel I ℓ₂ → (A → A) → DistanceFunction A I → Set _
StrictlyContracting _≈_ _<_ f d = ∀ {x y} → ¬ (y ≈ x) → d (f x) (f y) < d x y

StrictlyContractingOnOrbits : Rel A ℓ₁ → Rel I ℓ₂ → (A → A) → DistanceFunction A I → Set _
StrictlyContractingOnOrbits _≈_ _<_ f d = ∀ {x} → ¬ (f x ≈ x) → d (f x) (f (f x)) < d x (f x)
