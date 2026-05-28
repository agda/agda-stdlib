------------------------------------------------------------------------
-- The Agda standard library
--
-- Empty type, judgementally proof irrelevant, Level-monomorphic
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Empty where

open import Data.Irrelevant using (Irrelevant)

------------------------------------------------------------------------
-- Definition

-- Note that by default the empty type is not universe polymorphic as it
-- often results in unsolved metas. See `Data.Empty.Polymorphic` for a
-- universe polymorphic variant.

private
  data Empty : Prop where

-- ⊥ is defined via Data.Irrelevant (a record with a single irrelevant
-- field) so that Agda can judgementally declare that all proofs of ⊥
-- are equal to each other. In particular this means that all functions
-- returning a proof of ⊥ are equal.

record ⊥ : Set where
  constructor [_]
  field
    empty : Empty
open ⊥ public

{-# DISPLAY Irrelevant Empty = ⊥ #-}

------------------------------------------------------------------------
-- Functions

private
  empty-elim : ∀ {w} {Whatever : Set w} → .Empty → Whatever
  empty-elim ()

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim x = empty-elim (empty x)

⊥-elim-irr : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
⊥-elim-irr x = empty-elim (empty x)

