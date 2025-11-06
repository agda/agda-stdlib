------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty lists where at least one element satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.NonEmpty.Relation.Unary.Any where

open import Data.List.NonEmpty using (List⁺; _∷_)

open import Data.List.Relation.Unary.Any as List using (here; there)
open import Data.List.Base using ([]; _∷_)
open import Data.List.NonEmpty.Base using (List⁺; _∷_; toList)
open import Data.Product.Base using (_,_)
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred; Satisfiable; _⊆_)

private
  variable
    a p : Level
    A : Set a
    P Q : Pred A p
    xs : List⁺ A

------------------------------------------------------------------------
-- Definition

-- Given a predicate P, then Any P xs means that every element in xs
-- satisfies P. See `Relation.Unary` for an explanation of predicates.

data Any {A : Set a} (P : Pred A p) : Pred (List⁺ A) (a ⊔ p) where
  here : ∀ {x xs} (px : P x) → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : List.Any P xs) → Any P (x ∷ xs)

------------------------------------------------------------------------
-- Operations

map : P ⊆ Q → Any P ⊆ Any Q
map g (here px)   = here (g px)
map g (there pxs) = there (List.map g pxs)

------------------------------------------------------------------------
-- Predicates

satisfied : Any P xs → Satisfiable P
satisfied (here px)  = _ , px
satisfied (there pxs) = List.satisfied pxs
