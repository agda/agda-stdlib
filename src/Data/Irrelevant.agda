------------------------------------------------------------------------
-- The Agda standard library
--
-- Wrapper for the proof irrelevance modality
--
-- This allows us to store proof irrelevant witnesses in a record and
-- use projections to manipulate them without having to turn on the
-- unsafe option --irrelevant-projections.
-- Cf. Data.Refinement for a use case
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Irrelevant where

open import Level using (Level)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Type

record Irrelevant (A : Set a) : Set a where
  constructor [_]
  field .irrelevant : A
open Irrelevant public

------------------------------------------------------------------------
-- Algebraic structure: Functor, Appplicative and Monad-like

map : (A → B) → Irrelevant A → Irrelevant B
map f [ a ] = [ f a ]

pure : A → Irrelevant A
pure x = [ x ]

infixl 4 _<*>_
_<*>_ : Irrelevant (A → B) → Irrelevant A → Irrelevant B
[ f ] <*> [ a ] = [ f a ]

infixl 1 _>>=_
_>>=_ : Irrelevant A → (.A → Irrelevant B) → Irrelevant B
[ a ] >>= f = f a

------------------------------------------------------------------------
-- Other functions

zipWith : (A → B → C) → Irrelevant A → Irrelevant B → Irrelevant C
zipWith f a b = ⦇ f a b ⦈
