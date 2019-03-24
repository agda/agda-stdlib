------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of functions, such as associativity and
-- commutativity (only those that don't require any sort of setoid)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.FunctionProperties.Consequences.Core
  {a} {A : Set a} where

open import Algebra.FunctionProperties
open import Data.Sum
open import Relation.Binary

sel⇒idem : ∀ {ℓ} {_•_ : Op₂ A} (_≈_ : Rel A ℓ) →
           Selective _≈_ _•_ → Idempotent _≈_ _•_
sel⇒idem _ sel x with sel x x
... | inj₁ x•x≈x = x•x≈x
... | inj₂ x•x≈x = x•x≈x
