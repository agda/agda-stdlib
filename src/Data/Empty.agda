------------------------------------------------------------------------
-- The Agda standard library
--
-- Empty type, judgementally proof irrelevant, Level-monomorphic
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Empty where

------------------------------------------------------------------------
-- Definition

-- Note that by default the empty type is not universe polymorphic as it
-- often results in unsolved metas. See `Data.Empty.Polymorphic` for a
-- universe polymorphic variant.

private
  data Empty : Set where

-- ⊥ is defined a record with a single irrelevant so that Agda can judgementally
-- declare that all proofs of ⊥ are equal to each other. In particular this
-- means that all functions returning a proof of ⊥ are equal.

data ⊥ₚ : Prop where

-- TOOD: make a generic Prop → Set record
record ⊥ : Set where
  constructor [_]
  field bot : ⊥ₚ

------------------------------------------------------------------------
-- Functions

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()

⊥-elim-irr : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
⊥-elim-irr ()
