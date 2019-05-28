------------------------------------------------------------------------
-- The Agda standard library
--
-- Universe levels
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Level where

-- Levels.

open import Agda.Primitive as Prim public
  using    (Level; _⊔_; Setω)
  renaming (lzero to zero; lsuc to suc)

-- Lifting.

record Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public

-- Synonyms

0ℓ : Level
0ℓ = zero
