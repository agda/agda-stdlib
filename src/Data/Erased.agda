------------------------------------------------------------------------
-- The Agda standard library
--
-- Wrapper for the erased modality
--
-- This allows us to store erased proofs in a record and use projections
-- to manipulate them without having to turn on the unsafe option
-- --irrelevant-projections.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Erased where

open import Level using (Level)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Type

record Erased (A : Set a) : Set a where
  constructor [_]
  field .erased : A
open Erased public

------------------------------------------------------------------------
-- Algebraic structure: Functor, Appplicative and Monad-like

map : (A → B) → Erased A → Erased B
map f [ a ] = [ f a ]

pure : A → Erased A
pure x = [ x ]

infixl 4 _<*>_
_<*>_ : Erased (A → B) → Erased A → Erased B
[ f ] <*> [ a ] = [ f a ]

infixl 1 _>>=_
_>>=_ : Erased A → (.A → Erased B) → Erased B
[ a ] >>= f = f a

------------------------------------------------------------------------
-- Other functions

zipWith : (A → B → C) → Erased A → Erased B → Erased C
zipWith f a b = ⦇ f a b ⦈
