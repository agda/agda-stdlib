------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Permutation.Setoid
  {b} {ℓ} (S : Setoid b ℓ) where

open import Data.List using (List; _∷_)
import Data.List.Relation.Binary.Permutation.Homogeneous as HomogeneousPermutation
open import Level using (_⊔_)
import Relation.Binary.EqReasoning as EqReasoning

open Setoid S using (Carrier; _≈_; sym)

open HomogeneousPermutation
  using (refl; prep; swap; trans) public
open HomogeneousPermutation
  renaming (sym to Perm-sym;
            isEquivalence to Perm-isEquivalence;
            setoid to Perm-setoid)

infix 3 _↭_
_↭_ : Rel (List Carrier) (b ⊔ ℓ)
_↭_ = Permutation _≈_

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-refl : Reflexive (Permutation _≈_)
↭-refl = refl

↭-trans : Transitive (Permutation _≈_)
↭-trans = trans

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

