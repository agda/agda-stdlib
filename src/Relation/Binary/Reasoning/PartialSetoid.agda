------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for reasoning with a partial setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.PartialSetoid
  {s₁ s₂} (S : PartialSetoid s₁ s₂) where

open PartialSetoid S
import Relation.Binary.Reasoning.Base.Partial _≈_ trans as Base

------------------------------------------------------------------------
-- Re-export the contents of the base module

open Base public
  hiding (step-∼)

------------------------------------------------------------------------
-- Additional reasoning combinators

infixr 2 step-≈ step-≈˘

-- A step using an equality

step-≈ = Base.step-∼
syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

-- A step using a symmetric equality

step-≈˘ : ∀ x {y z} → y IsRelatedTo z → y ≈ x → x IsRelatedTo z
step-≈˘ x y∼z y≈x = x ≈⟨ sym y≈x ⟩ y∼z
syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z
