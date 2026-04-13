------------------------------------------------------------------------
-- The Agda standard library
--
-- Negation indexed by a Level
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Indexed where

open import Data.Empty hiding (⊥-elim)
open import Level

------------------------------------------------------------------------
-- Negation.

-- level polymorphic version of ¬
¬ : ∀ {ℓ} (b : Level) → Set ℓ → Set (ℓ ⊔ b)
¬ b P = P → Lift b ⊥
