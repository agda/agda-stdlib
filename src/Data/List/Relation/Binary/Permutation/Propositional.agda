------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition for the permutation relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Permutation.Propositional
  {a} {A : Set a} where

open import Data.List.Base using (List; []; _∷_)
import Data.List.Relation.Binary.Permutation.Homogeneous as Homogeneous
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as EqReasoning


------------------------------------------------------------------------
-- Definition

infix 3 _↭_

_↭_ : Rel (List A) a
_↭_ = Homogeneous.Permutation _≡_ _≡_

pattern refl = Homogeneous.refl Eq.refl
pattern prep x tl = Homogeneous.prep {x = x} Eq.refl tl
pattern swap x y tl = Homogeneous.swap {x = x} {y = y} Eq.refl Eq.refl tl

open Homogeneous public
  using (trans)

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive Eq.refl = refl

↭-refl : Reflexive _↭_
↭-refl = refl

↭-sym : ∀ {xs ys} → xs ↭ ys → ys ↭ xs
↭-sym = Homogeneous.sym Eq.sym Eq.sym

-- A smart version of trans that avoids unnecessary `refl`s (see #1113).
↭-trans : Transitive _↭_
↭-trans refl ρ₂ = ρ₂
↭-trans ρ₁ refl = ρ₁
↭-trans ρ₁ ρ₂   = trans ρ₁ ρ₂

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = record
  { refl  = refl
  ; sym   = ↭-sym
  ; trans = ↭-trans
  }

↭-setoid : Setoid _ _
↭-setoid = record
  { isEquivalence = ↭-isEquivalence
  }

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs and allow "zooming in"
-- to localised reasoning.

module PermutationReasoning where

  private
    module Base = EqReasoning ↭-setoid

  open EqReasoning ↭-setoid public
    hiding (step-≈; step-≈˘)

  infixr 2 step-↭  step-↭˘ step-swap step-prep

  step-↭  = Base.step-≈
  step-↭˘ = Base.step-≈˘

  -- Skip reasoning on the first element
  step-prep : ∀ x xs {ys zs : List A} → (x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ xs) IsRelatedTo zs
  step-prep x xs rel xs↭ys = relTo (trans (prep x xs↭ys) (begin rel))

  -- Skip reasoning about the first two elements
  step-swap : ∀ x y xs {ys zs : List A} → (y ∷ x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ y ∷ xs) IsRelatedTo zs
  step-swap x y xs rel xs↭ys = relTo (trans (swap x y xs↭ys) (begin rel))

  syntax step-↭  x y↭z x↭y = x ↭⟨  x↭y ⟩ y↭z
  syntax step-↭˘ x y↭z y↭x = x ↭˘⟨  y↭x ⟩ y↭z
  syntax step-prep x xs y↭z x↭y = x ∷ xs <⟨ x↭y ⟩ y↭z
  syntax step-swap x y xs y↭z x↭y = x ∷ y ∷ xs <<⟨ x↭y ⟩ y↭z
