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

open Setoid S using (_≈_; sym)

open HomogeneousPermutation _≈_
  using (_↭_; refl; prep; swap; trans; ↭-refl; ↭-trans) public
open HomogeneousPermutation _≈_
  using () renaming (↭-sym to ↭ₕ-sym;
            ↭-isEquivalence to ↭ₕ-isEquivalence;
            ↭-setoid to ↭ₕ-setoid)

↭-sym : Symmetric _↭_
↭-sym = ↭ₕ-sym sym

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = ↭ₕ-isEquivalence sym

↭-setoid : Setoid _ _
↭-setoid = ↭ₕ-setoid sym

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs

module PermutationReasoning where

  open EqReasoning ↭-setoid public
    using (begin_ ; _∎ ; _≡⟨⟩_; _≡⟨_⟩_)
    renaming (_≈⟨_⟩_ to _↭⟨_⟩_)

