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
  renaming (_∼⟨_⟩_ to _≈⟨_⟩_)

infixr 2 _≈˘⟨_⟩_

_≈˘⟨_⟩_ : ∀ x {y z} → y ≈ x → y IsRelatedTo z → x IsRelatedTo z
x ≈˘⟨ x≈y ⟩ y∼z = x ≈⟨ sym x≈y ⟩ y∼z
