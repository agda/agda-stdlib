------------------------------------------------------------------------
-- The Agda standard library
--
-- Permutation relations over Vector
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Relation.Binary.Permutation where

open import Level using (Level)
open import Data.Product.Base using (Σ-syntax)
open import Data.Fin.Permutation using (Permutation; _⟨$⟩ʳ_)
open import Data.Vec.Functional using (Vector)
open import Relation.Binary.Indexed.Heterogeneous.Core using (IRel)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    ℓ : Level
    A : Set ℓ

infix 3 _↭_

_↭_ : IRel (Vector A) _
xs ↭ ys = Σ[ ρ ∈ Permutation _ _ ] (∀ i → xs (ρ ⟨$⟩ʳ i) ≡ ys i)
