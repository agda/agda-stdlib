------------------------------------------------------------------------
-- The Agda standard library
--
-- Empty type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Empty where

open import Level

data ⊥ : Set where

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()
