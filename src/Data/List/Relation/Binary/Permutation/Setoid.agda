------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List using (List; _∷_)
import Data.List.Relation.Binary.Permutation.Homogeneous as HomogeneousPermutation
open import Level using (_⊔_)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqReasoning

module Data.List.Relation.Binary.Permutation.Setoid
  {b} {ℓ} (S : Setoid b ℓ) where

open Setoid S using (Carrier; _≈_; sym)

open HomogeneousPermutation
  using (refl; prep; swap; trans)
  renaming (Perm-refl to ↭-refl; Perm-trans to ↭-trans) public
open HomogeneousPermutation

infix 3 _↭_
_↭_ : Rel (List Carrier) (b ⊔ ℓ)
_↭_ = Permutation _≈_

↭-sym : Symmetric (Permutation _≈_)
↭-sym = Perm-sym sym

↭-isEquivalence : IsEquivalence (Permutation _≈_)
↭-isEquivalence = Perm-isEquivalence sym

↭-setoid : Setoid _ _
↭-setoid = Perm-setoid {R = _≈_} sym

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs

module PermutationReasoning where

  open EqReasoning ↭-setoid public
    using (begin_ ; _∎ ; _≡⟨⟩_; _≡⟨_⟩_)
    renaming (_≈⟨_⟩_ to _↭⟨_⟩_)

