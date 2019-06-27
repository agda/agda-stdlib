------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Permutation.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open import Data.List using (List; _∷_)
import Data.List.Relation.Binary.Permutation.Homogeneous as Homogeneous
open import Data.List.Relation.Binary.Equality.Setoid S
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

private
  module Eq = Setoid S
open Eq using (_≈_) renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition

open Homogeneous public
  using (refl; prep; swap; trans)

infix 3 _↭_

_↭_ : Rel (List A) (a ⊔ ℓ)
_↭_ = Homogeneous.Permutation _≈_

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive refl = refl

↭-refl : Reflexive _↭_
↭-refl = ↭-reflexive refl

↭-sym : Symmetric _↭_
↭-sym = Homogeneous.sym Eq.sym

↭-trans : Transitive _↭_
↭-trans = trans

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = Homogeneous.isEquivalence Eq.sym

↭-setoid : Setoid _ _
↭-setoid = Homogeneous.setoid {R = _≈_} Eq.sym

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs

module PermutationReasoning where

  open SetoidReasoning ↭-setoid
    using (_IsRelatedTo_; relTo)

  open SetoidReasoning ↭-setoid public
    using (begin_ ; _∎ ; _≡⟨⟩_; _≡⟨_⟩_)
    renaming (_≈⟨_⟩_ to _↭⟨_⟩_; _≈˘⟨_⟩_ to _↭˘⟨_⟩_)

  infixr 2 _∷_<⟨_⟩_  _∷_∷_<<⟨_⟩_

  -- Skip reasoning on the first element
  _∷_<⟨_⟩_ : ∀ x xs {ys zs : List A} → xs ↭ ys →
               (x ∷ ys) IsRelatedTo zs → (x ∷ xs) IsRelatedTo zs
  x ∷ xs <⟨ xs↭ys ⟩ rel = relTo (trans (prep Eq.refl xs↭ys) (begin rel))

  -- Skip reasoning about the first two elements
  _∷_∷_<<⟨_⟩_ : ∀ x y xs {ys zs : List A} → xs ↭ ys →
                  (y ∷ x ∷ ys) IsRelatedTo zs → (x ∷ y ∷ xs) IsRelatedTo zs
  x ∷ y ∷ xs <<⟨ xs↭ys ⟩ rel = relTo (trans (swap Eq.refl Eq.refl xs↭ys) (begin rel))

