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
-- is recommended for equational reasoning when the underlying equality
-- is `_≡_`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Reasoning.Syntax using (module ≈-syntax)

module Relation.Binary.Reasoning.Setoid {s₁ s₂} (S : Setoid s₁ s₂) where

open Setoid S

import Relation.Binary.Reasoning.Base.Single _≈_ refl trans
  as SingleRelReasoning

------------------------------------------------------------------------
-- Reasoning combinators

-- Export the combinators for single relation reasoning, hiding the
-- single misnamed combinator.
open SingleRelReasoning public
  hiding (step-∼)
  renaming (∼-go to ≈-go)

-- Re-export the equality-based combinators instead
open ≈-syntax _IsRelatedTo_ _IsRelatedTo_ ≈-go sym public
