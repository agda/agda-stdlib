------------------------------------------------------------------------
-- The Agda standard library
--
-- Results concerning double negation elimination.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Axiom.DoubleNegationElimination where

open import Axiom.ExcludedMiddle
open import Level
open import Relation.Nullary
open import Relation.Nullary.Negation

------------------------------------------------------------------------
-- Definition

-- The classical statement of double negation elimination says that
-- if a property is not not true then it is true.

DoubleNegationElimination : (ℓ : Level) → Set (suc ℓ)
DoubleNegationElimination ℓ = {P : Set ℓ} → ¬ ¬ P → P

------------------------------------------------------------------------
-- Properties

-- Double negation elimination is equivalent to excluded middle

em⇒dne : ∀ {ℓ} → ExcludedMiddle ℓ → DoubleNegationElimination ℓ
em⇒dne em = decidable-stable em

dne⇒em : ∀ {ℓ} → DoubleNegationElimination ℓ → ExcludedMiddle ℓ
dne⇒em dne = dne excluded-middle
