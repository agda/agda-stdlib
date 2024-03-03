------------------------------------------------------------------------
-- The Agda standard library
--
-- Polymorphic versions of standard definitions in Relation.Unary
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Polymorphic where

open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level)
open import Relation.Unary using (Pred)

private
  variable
    a ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- Special sets

-- The empty set.

∅ : Pred A ℓ
∅ = λ _ → ⊥

-- The universal set.

U : Pred A ℓ
U = λ _ → ⊤
