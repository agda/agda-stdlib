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
-- Publicly re-export base contents

open import Relation.Binary.Reasoning.Base.Single _≈_ refl trans public
  renaming (_∼⟨_⟩_ to _≈⟨_⟩_)

------------------------------------------------------------------------
-- Combinator for avoiding the use of `sym`

infixr 2 _≈˘⟨_⟩_

_≈˘⟨_⟩_ : ∀ x {y z} → y ≈ x → y IsRelatedTo z → x IsRelatedTo z
x ≈˘⟨ x≈y ⟩ y∼z = x ≈⟨ sym x≈y ⟩ y∼z

------------------------------------------------------------------------
-- Combinator for reflective solvers.

-- This combinator is for use with the reflective solvers. See
-- README.Solver.ReflectiveMonoid for examples. This additional
-- combinator is required because the standard _≈⟨_⟩_ combinator infers
-- the RHS of the equational step from the LHS + the type of the proof.
-- Therefore the reflection machinary cannot determine what it is
-- supposed to prove. In contrast _≈!⟨_⟩_ infers the type of the proof
-- from the LHS + RHS of the equational step.

-- Consequently this combinator is also more efficient than the
-- standard _≈⟨_⟩_ combinator. Unfortunately _≈⟨_⟩_ has not been
-- replaced by _≈!⟨_⟩_ because of the current inability to rename
-- syntax declarations which make re-exporting such combinators
-- difficult.

infixr 2 ≈-step
≈-step : ∀ x {y z} → y IsRelatedTo z → x ≈ y → x IsRelatedTo z
≈-step x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

syntax ≈-step x y≈z x≈y = x ≈!⟨ x≈y ⟩ y≈z
