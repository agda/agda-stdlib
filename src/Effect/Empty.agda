------------------------------------------------------------------------
-- The Agda standard library
--
-- Empty values (e.g. [] for List, nothing for Maybe)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Empty where

open import Level

private
  variable
    ℓ ℓ′ : Level
    A  : Set ℓ

record RawEmpty (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  field
    empty : F A

  -- backwards compatibility: unicode variants
  ∅ : F A
  ∅ = empty
