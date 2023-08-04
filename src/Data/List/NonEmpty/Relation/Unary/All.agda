------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty lists where all elements satisfy a given property
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.NonEmpty.Relation.Unary.All where

import Data.List.Relation.Unary.All as List
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Base using ([]; _∷_)
open import Data.List.NonEmpty.Base using (List⁺; _∷_; toList)
open import Level
open import Relation.Unary using (Pred)

private
  variable
    a p : Level
    A : Set a
    P : Pred A p

------------------------------------------------------------------------
-- Definition

-- Given a predicate P, then All P xs means that every element in xs
-- satisfies P. See `Relation.Unary` for an explanation of predicates.

infixr 5 _∷_

data All {A : Set a} (P : Pred A p) : Pred (List⁺ A) (a ⊔ p) where
  _∷_ : ∀ {x xs} (px : P x) (pxs : List.All P xs) → All P (x ∷ xs)

------------------------------------------------------------------------
-- Functions

toList⁺ : ∀ {xs : List⁺ A} → All P xs → List.All P (toList xs)
toList⁺ (px ∷ pxs) = px ∷ pxs
