------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the sublist relation. This is commonly
-- known as an Order Preserving Embedding (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional {a} {A : Set a} where

open import Data.List.Base using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.Any  using (here; there)
open import Data.List.Membership.Propositional
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (refl)

------------------------------------------------------------------------
-- Type and basic combinators

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

-- Conversion between membership and proofs that a singleton is a sublist

from∈ : ∀ {xs x} → x ∈ xs → [ x ] ⊆ xs
from∈ (here refl) = keep ([]⊆ _)
from∈ (there p)   = skip (from∈ p)

to∈ : ∀ {xs x} → [ x ] ⊆ xs → x ∈ xs
to∈ p = lookup p (here refl)
