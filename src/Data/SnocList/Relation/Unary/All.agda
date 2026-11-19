------------------------------------------------------------------------
-- The Agda standard library
--
-- SnocLists where all elements satisfy a given property
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.SnocList.Relation.Unary.All where

open import Data.SnocList.Base
open import Relation.Unary using (Pred; ∅)
open import Level using (Level; suc; _⊔_)

private
  variable
    a b p q r ℓ : Level
    A : Set a
    B : Set b
    P Q R : Pred A p
    x : A
    xs : List< A

------------------------------------------------------------------------
-- Definitions

-- Given a predicate P, then All P xs means that every element in xs
-- satisfies P. See `Relation.Unary` for an explanation of predicates.
--
-- Equivalent to the definition on List>, but now for List<

infixr 5 _<:_

data All< {A : Set a} (P : Pred A p) : Pred (List< A) (a ⊔ p) where
  []  : All< P []
  _<:_ : ∀ {x xs} (px : P x) (pxs : All< P xs) → All< P (xs <: x)

Null< : Pred (List< A) _
Null< = All< ∅
