------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of sublist. This is commonly known as an Order
-- Preserving Embedding (OPE).
------------------------------------------------------------------------

module Data.List.Relation.Sublist.Inductive where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Any  using (here; there)
open import Data.List.Membership.Propositional
open import Relation.Binary using (Rel)

------------------------------------------------------------------------
-- Type and basic combinators

module _ {a} {A : Set a} where

  infix 3 _⊆_
  data _⊆_ : Rel (List A) a where
    base : [] ⊆ []
    skip : ∀ {xs y ys} → xs ⊆ ys → xs ⊆ (y ∷ ys)
    keep : ∀ {x xs ys} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)

  infix 4 []⊆_
  []⊆_ : ∀ xs → [] ⊆ xs
  []⊆ []     = base
  []⊆ x ∷ xs = skip ([]⊆ xs)

------------------------------------------------------------------------
-- A function induced by a sublist proof

  lookup : ∀ {xs ys} → xs ⊆ ys → {x : A} → x ∈ xs → x ∈ ys
  lookup (skip p) v         = there (lookup p v)
  lookup (keep p) (here px) = here px
  lookup (keep p) (there v) = there (lookup p v)
  lookup base     ()
