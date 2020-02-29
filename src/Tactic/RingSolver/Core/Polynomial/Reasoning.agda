------------------------------------------------------------------------
-- The Agda standard library
--
-- Polynomial reasoning
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.AlmostCommutativeRing

-- Some specialised tools for equational reasoning.
module Tactic.RingSolver.Core.Polynomial.Reasoning
  {a ℓ} (ring : AlmostCommutativeRing a ℓ)
  where

open AlmostCommutativeRing ring
open import Relation.Binary.Reasoning.Setoid setoid public

infixr 1 ≪+_ +≫_ ≪*_ *≫_
infixr 0 _⊙_

≪+_ : ∀ {x₁ x₂ y} → x₁ ≈ x₂ → x₁ + y ≈ x₂ + y
≪+ prf = +-cong prf refl
{-# INLINE ≪+_ #-}

+≫_ : ∀ {x y₁ y₂} → y₁ ≈ y₂ → x + y₁ ≈ x + y₂
+≫_ = +-cong refl
{-# INLINE +≫_ #-}

≪*_ : ∀ {x₁ x₂ y} → x₁ ≈ x₂ → x₁ * y ≈ x₂ * y
≪* prf = *-cong prf refl
{-# INLINE ≪*_ #-}

*≫_ : ∀ {x y₁ y₂} → y₁ ≈ y₂ → x * y₁ ≈ x * y₂
*≫_ = *-cong refl
{-# INLINE *≫_ #-}

-- transitivity as an operator
_⊙_ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
_⊙_ = trans
{-# INLINE _⊙_ #-}
