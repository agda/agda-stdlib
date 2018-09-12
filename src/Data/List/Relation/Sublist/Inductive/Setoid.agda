------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of sublist. This is commonly known as an Order
-- Preserving Embedding (OPE).
------------------------------------------------------------------------

open import Relation.Binary using (Rel; Setoid)

module Data.List.Relation.Sublist.Inductive.Setoid
       {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Base using (List; []; _∷_; [_])
open import Data.List.Any  using (here; there)
open import Data.List.Membership.Setoid S

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Type and basic combinators

infix 3 _⊆_
data _⊆_ : Rel (List A) ℓ where
  base : [] ⊆ []
  skip : ∀ {xs y ys} → xs ⊆ ys → xs ⊆ (y ∷ ys)
  keep : ∀ {x y xs ys} → x ≈ y → xs ⊆ ys → (x ∷ xs) ⊆ (y ∷ ys)

infix 4 []⊆_
[]⊆_ : ∀ xs → [] ⊆ xs
[]⊆ []     = base
[]⊆ x ∷ xs = skip ([]⊆ xs)

------------------------------------------------------------------------
-- A function induced by a sublist proof

lookup : ∀ {xs ys} → xs ⊆ ys → {x : A} → x ∈ xs → x ∈ ys
lookup (skip p)     v          = there (lookup p v)
lookup (keep x≈y p) (here z≈x) = here (trans z≈x x≈y)
lookup (keep x≈y p) (there v)  = there (lookup p v)
lookup base         ()

-- Conversion between membership and proofs that a singleton is a sublist

from∈ : ∀ {xs x} → x ∈ xs → [ x ] ⊆ xs
from∈ (here x≈y) = keep x≈y ([]⊆ _)
from∈ (there p)  = skip (from∈ p)

to∈ : ∀ {xs x} → [ x ] ⊆ xs → x ∈ xs
to∈ p = lookup p (here refl)
