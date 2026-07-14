------------------------------------------------------------------------
-- The Agda standard library
--
-- Morphisms between algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Morphism where

import Algebra.Morphism.Definitions as MorphismDefinitions
open import Algebra
open import Function.Base
open import Level
open import Relation.Binary.Core using (Rel; _Preserves_⟶_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    a b ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Re-export

module Definitions {a b ℓ₁} (A : Set a) (B : Set b) (_≈_ : Rel B ℓ₁) where
  open MorphismDefinitions A B _≈_ public

open import Algebra.Morphism.Structures public
