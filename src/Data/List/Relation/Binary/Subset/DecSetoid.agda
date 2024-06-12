------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidability of the subset relation over setoid equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecSetoid)

module Data.List.Relation.Binary.Subset.DecSetoid {c ℓ} (S : DecSetoid c ℓ) where

open import Function.Base using (_∘_)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there; map)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (yes; no)
open DecSetoid S
open import Data.List.Relation.Binary.Equality.DecSetoid S
open import Data.List.Membership.DecSetoid S

-- Re-export definitions
open import Data.List.Relation.Binary.Subset.Setoid setoid public

infix 4 _⊆?_
_⊆?_ : Decidable _⊆_
[]       ⊆? _   = yes λ ()
(x ∷ xs) ⊆? ys  with x ∈? ys
... | no  x∉ys  = no λ xs⊆ys → x∉ys (xs⊆ys (here refl))
... | yes x∈ys  with xs ⊆? ys
...   | no  xs⊈ys = no λ xs⊆ys → xs⊈ys (xs⊆ys ∘ there)
...   | yes xs⊆ys = yes λ where (here refl) → map (trans refl) x∈ys
                                (there x∈)  → xs⊆ys x∈
