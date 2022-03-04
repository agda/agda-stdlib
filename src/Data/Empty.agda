------------------------------------------------------------------------
-- The Agda standard library
--
-- Empty type, judgementally proof irrelevant
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Empty where

open import Data.Erased using (Erased)

------------------------------------------------------------------------
-- Definition

-- Note that by default the empty type is not universe polymorphic as it
-- often results in unsolved metas. See `Data.Empty.Polymorphic` for a
-- universe polymorphic variant.

private
  data Empty : Set where

-- ⊥ is defined via Data.Erased (a record with a single irrelevant field)
-- so that Agda can judgementally declare that all proofs of ⊥ are equal
-- to each other. In particular this means that all functions returning a
-- proof of ⊥ are equal.

⊥ : Set
⊥ = Erased Empty

{-# DISPLAY Erased Empty = ⊥ #-}

------------------------------------------------------------------------
-- Functions

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()
