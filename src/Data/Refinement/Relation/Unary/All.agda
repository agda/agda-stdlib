------------------------------------------------------------------------
-- The Agda standard library
--
-- Predicate lifting for refinement types
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Refinement.Relation.Unary.All where

open import Data.Refinement using (Refinement; _,_)
open import Level using (Level; _⊔_)
open import Function.Base using (const)

private
  variable
    a b p q : Level
    A : Set a
    B : Set b

module _ {P : A → Set p} where

  All : (A → Set q) → Refinement A P → Set q
  All P (a , _) = P a
