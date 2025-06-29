------------------------------------------------------------------------
-- The Agda standard library
--
-- Recomputable types and their algebra as Harrop formulas
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Recomputable.Core where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Level)
open import Relation.Nullary.Irrelevant using (Irrelevant)

private
  variable
    a : Level
    A : Set a


------------------------------------------------------------------------
-- Definition
--
-- The idea of being 'recomputable' is that, given an *irrelevant* proof
-- of a proposition `A` (signalled by being a value of type `.A`, all of
-- whose inhabitants are identified up to definitional equality, and hence
-- do *not* admit pattern-matching), one may 'promote' such a value to a
-- 'genuine' value of `A`, available for subsequent eg. pattern-matching.

Recomputable : (A : Set a) → Set a
Recomputable A = .A → A

------------------------------------------------------------------------
-- Fundamental properties:
-- given `Recomputable A`, `recompute` is a constant function;
-- moreover, the identity, if `A` is propositionally irrelevant.

module _ (recompute : Recomputable A) where

  recompute-constant : (p q : A) → recompute p ≡ recompute q
  recompute-constant _ _ = refl

  recompute-irrelevant-id : Irrelevant A → (a : A) → recompute a ≡ a
  recompute-irrelevant-id irr a = irr (recompute a) a

