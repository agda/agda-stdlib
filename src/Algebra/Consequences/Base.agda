------------------------------------------------------------------------
-- The Agda standard library
--
-- Lemmas relating algebraic definitions (such as associativity and
-- commutativity) that don't the equality relation to be a setoid.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Consequences.Base
  {a} {A : Set a} where

open import Algebra.Core
open import Algebra.Definitions
open import Data.Sum.Base
open import Relation.Binary.Core

sel⇒idem : ∀ {ℓ} {_•_ : Op₂ A} (_≈_ : Rel A ℓ) →
           Selective _≈_ _•_ → Idempotent _≈_ _•_
sel⇒idem _ sel x with sel x x
... | inj₁ x•x≈x = x•x≈x
... | inj₂ x•x≈x = x•x≈x
