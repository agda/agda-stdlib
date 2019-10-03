------------------------------------------------------------------------
-- The Agda standard library
--
-- Level polymorphic Empty type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Empty.Polymorphic where

open import Level

data ⊥ {ℓ : Level} : Set ℓ where

⊥-elim : ∀ {w ℓ} {Whatever : Set w} → ⊥ {ℓ} → Whatever
⊥-elim ()
