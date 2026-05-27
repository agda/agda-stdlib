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

module Data.Squash where

open import Level using (Level)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Type

data Squash (A : Set a) : Prop a where
  squash : A → Squash A

------------------------------------------------------------------------
-- Algebraic structure: Functor, Appplicative and Monad-like

map : (A → B) → Squash A → Squash B
map f (squash x) = squash (f x)

infixl 4 _<*>_
_<*>_ : Squash (A → B) → Squash A → Squash B
squash f <*> squash x = squash (f x)

infixl 1 _>>=_
_>>=_ : Squash A → (A → Squash B) → Squash B
squash x >>= f = f x

