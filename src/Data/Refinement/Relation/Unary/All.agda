------------------------------------------------------------------------
-- The Agda standard library
--
-- Predicate lifting for refinement types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Refinement.Relation.Unary.All where

open import Level
open import Data.Refinement
open import Function.Base
open import Relation.Unary

private
  variable
    a b p q : Level
    A : Set a
    B : Set b

module _ {P : A → Set p} where

  All : (A → Set q) → Refinement A P → Set q
  All P (a , _) = P a
