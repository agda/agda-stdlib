------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Permutation.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open import Data.List.Base using (List; _∷_)
import Data.List.Relation.Binary.Permutation.Homogeneous as Homogeneous
import Data.List.Relation.Binary.Pointwise as Pointwise
open import Data.List.Relation.Binary.Equality.Setoid S
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
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
-- Constructor aliases

-- These provide aliases for `swap` and `prep` when the elements being
-- swapped or prepended are propositionally equal

↭-prep : ∀ x {xs ys} → xs ↭ ys → x ∷ xs ↭ x ∷ ys
↭-prep x xs↭ys = prep Eq.refl xs↭ys

↭-swap : ∀ x y {xs ys} → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
↭-swap x y xs↭ys = swap Eq.refl Eq.refl xs↭ys

------------------------------------------------------------------------
-- Functions over permutations

steps : ∀ {xs ys} → xs ↭ ys → ℕ
steps (refl _)            = 1
steps (prep _ xs↭ys)      = suc (steps xs↭ys)
steps (swap _ _ xs↭ys)    = suc (steps xs↭ys)
steps (trans xs↭ys ys↭zs) = steps xs↭ys + steps ys↭zs

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive refl = refl (Pointwise.refl Eq.refl)

↭-refl : Reflexive _↭_
↭-refl = ↭-reflexive refl

↭-sym : Symmetric _↭_
↭-sym = Homogeneous.sym Eq.sym

↭-trans : Transitive _↭_
↭-trans = trans

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = Homogeneous.isEquivalence Eq.refl Eq.sym

↭-setoid : Setoid _ _
↭-setoid = Homogeneous.setoid {R = _≈_} Eq.refl Eq.sym

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs

module PermutationReasoning where

  private
    module Base = SetoidReasoning ↭-setoid

  open SetoidReasoning ↭-setoid public
    hiding (step-≈; step-≈˘)

  infixr 2 step-↭  step-↭˘ step-≋ step-≋˘ step-swap step-prep

  step-↭  = Base.step-≈
  step-↭˘ = Base.step-≈˘

  -- Step with pointwise list equality
  step-≋ : ∀ x {y z} → y IsRelatedTo z → x ≋ y → x IsRelatedTo z
  step-≋ x (relTo y↔z) x≋y = relTo (trans (refl x≋y) y↔z)

  -- Step with flipped pointwise list equality
  step-≋˘ : ∀ x {y z} → y IsRelatedTo z → y ≋ x → x IsRelatedTo z
  step-≋˘ x y↭z y≋x = x ≋⟨ ≋-sym y≋x ⟩ y↭z

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
  syntax step-≋  x y↭z x≋y = x ≋⟨  x≋y ⟩ y↭z
  syntax step-≋˘ x y↭z y≋x = x ≋˘⟨  y≋x ⟩ y↭z
  syntax step-prep x xs y↭z x↭y = x ∷ xs <⟨ x↭y ⟩ y↭z
  syntax step-swap x y xs y↭z x↭y = x ∷ y ∷ xs <<⟨ x↭y ⟩ y↭z
