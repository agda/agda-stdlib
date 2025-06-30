------------------------------------------------------------------------
-- The Agda standard library
--
-- Results concerning double negation elimination.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Axiom.DoubleNegationElimination where

open import Axiom.ExcludedMiddle using (ExcludedMiddle)
open import Level using (Level; suc)
open import Relation.Nullary.Decidable.Core
  using (decidable-stable; ¬¬-excluded-middle)
open import Relation.Nullary.Negation.Core using (Stable)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Definition

-- The classical statement of double negation elimination says that
-- if a property is not not true then it is true.

DoubleNegationElimination : ∀ ℓ → Set (suc ℓ)
DoubleNegationElimination ℓ = {P : Set ℓ} → Stable P

------------------------------------------------------------------------
-- Properties

-- Double negation elimination is equivalent to excluded middle

em⇒dne : ExcludedMiddle ℓ → DoubleNegationElimination ℓ
em⇒dne em = decidable-stable em

dne⇒em : DoubleNegationElimination ℓ → ExcludedMiddle ℓ
dne⇒em dne = dne ¬¬-excluded-middle
