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

-- Module ≡-Reasoning in Relation.Binary.PropositionalEquality
-- is recommended for equational reasoning when the underlying equality is
-- `_≡_`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.Setoid {s₁ s₂} (S : Setoid s₁ s₂) where

open Setoid S

------------------------------------------------------------------------
-- Publicly re-export base contents

open import Relation.Binary.Reasoning.Base.Single _≈_ refl trans public
  hiding (step-∼)

infixr 2 step-≈ step-≈˘

step-≈ : ∀ x {y z} → y IsRelatedTo z → x ≈ y → x IsRelatedTo z
step-≈ _ (relTo y≈z) x≈y = relTo (trans x≈y y≈z)

syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

step-≈˘ : ∀ x {y z} → y IsRelatedTo z → y ≈ x → x IsRelatedTo z
step-≈˘ _ (relTo y≈z) y≈x = relTo (trans (sym y≈x) y≈z)

syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z
