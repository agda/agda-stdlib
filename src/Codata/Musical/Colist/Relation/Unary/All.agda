------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive lists where all elements satisfy a predicate
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module Codata.Musical.Colist.Relation.Unary.All where

open import Codata.Musical.Colist.Base
open import Codata.Musical.Notation
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred)

private
  variable
    a b p : Level
    A : Set a
    B : Set b
    P : Pred A p

data All {A : Set a} (P : Pred A p) : Pred (Colist A) (a ⊔ p) where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : ∞ (All P (♭ xs))) → All P (x ∷ xs)
