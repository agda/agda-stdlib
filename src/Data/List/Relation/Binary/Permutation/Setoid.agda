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

  private
    module Base = SetoidReasoning ↭-setoid

  open SetoidReasoning ↭-setoid public
    hiding (step-≈; step-≈˘)

  infixr 2 step-↭  step-↭˘ step-swap step-prep

  step-↭  = Base.step-≈
  step-↭˘ = Base.step-≈˘

  -- Skip reasoning on the first element
  step-prep : ∀ x xs {ys zs : List A} → (x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ xs) IsRelatedTo zs
  step-prep x xs rel xs↭ys = relTo (trans (prep Eq.refl xs↭ys) (begin rel))

  -- Skip reasoning about the first two elements
  step-swap : ∀ x y xs {ys zs : List A} → (y ∷ x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ y ∷ xs) IsRelatedTo zs
  step-swap x y xs rel xs↭ys = relTo (trans (swap Eq.refl Eq.refl xs↭ys) (begin rel))

  syntax step-↭  x y↭z x↭y = x ↭⟨  x↭y ⟩ y↭z
  syntax step-↭˘ x y↭z y↭x = x ↭˘⟨  y↭x ⟩ y↭z
  syntax step-prep x xs y↭z x↭y = x ∷ xs <⟨ x↭y ⟩ y↭z
  syntax step-swap x y xs y↭z x↭y = x ∷ y ∷ xs <<⟨ x↭y ⟩ y↭z
