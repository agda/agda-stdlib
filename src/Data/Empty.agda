------------------------------------------------------------------------
-- The Agda standard library
--
-- Empty type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Empty where

------------------------------------------------------------------------
-- Definition

-- Note that by default the empty type is not universe polymorphic as it
-- often results in unsolved metas. See `Data.Empty.Polymorphic` for a
-- universe polymorphic variant.

data ⊥ : Set where

------------------------------------------------------------------------
-- Functions

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()
