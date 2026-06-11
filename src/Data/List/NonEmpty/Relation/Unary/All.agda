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
open import Data.List.NonEmpty.Membership.Propositional using (_∈_)
open import Data.List.NonEmpty.Relation.Unary.Any using (here; there)
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred; _⊆_)
open import Relation.Binary.PropositionalEquality.Core using (refl)

private
  variable
    a p : Level
    A : Set a
    P Q : Pred A p
    xs : List⁺ A

------------------------------------------------------------------------
-- Definition

-- Given a predicate P, then All P xs means that every element in xs
-- satisfies P. See `Relation.Unary` for an explanation of predicates.

infixr 5 _∷_

data All {A : Set a} (P : Pred A p) : Pred (List⁺ A) (a ⊔ p) where
  _∷_ : ∀ {x xs} (px : P x) (pxs : List.All P xs) → All P (x ∷ xs)

------------------------------------------------------------------------
-- Functions

map : P ⊆ Q → All P ⊆ All Q
map P⊆Q (px ∷ pxs) = P⊆Q px ∷ List.map P⊆Q pxs

lookup : All P xs → ∀ {x} → x ∈ xs → P x
lookup (px ∷ pxs) (here refl)   = px
lookup (px ∷ pxs) (there x∈xs) = List.lookup pxs x∈xs

toList⁺ : ∀ {xs : List⁺ A} → All P xs → List.All P (toList xs)
toList⁺ (px ∷ pxs) = px ∷ pxs
