------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for reasoning with a setoid
------------------------------------------------------------------------

-- Example use:

-- n*0≡0 : ∀ n → n * 0 ≡ 0
-- n*0≡0 zero    = refl
-- n*0≡0 (suc n) = begin
--   suc n * 0 ≈⟨ refl ⟩
--   n * 0 + 0 ≈⟨ ... ⟩
--   n * 0     ≈⟨ n*0≡0 n ⟩
--   0         ∎

-- Module `≡-Reasoning` in `Relation.Binary.PropositionalEquality`
-- is recommended for equational reasoning when the underlying equality is
-- `_≡_`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.Setoid {s₁ s₂} (S : Setoid s₁ s₂) where

open Setoid S

------------------------------------------------------------------------
-- Reasoning combinators

-- open import Relation.Binary.Reasoning.PartialSetoid partialSetoid public
open import Relation.Binary.Reasoning.Base.Single _≈_ refl trans as Base public
  hiding (step-∼)

infixr 2 step-≈ step-≈˘

-- A step using an equality

step-≈ = Base.step-∼
syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

-- A step using a symmetric equality

step-≈˘ : ∀ x {y z} → y IsRelatedTo z → y ≈ x → x IsRelatedTo z
step-≈˘ x y∼z y≈x = x ≈⟨ sym y≈x ⟩ y∼z
syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z
