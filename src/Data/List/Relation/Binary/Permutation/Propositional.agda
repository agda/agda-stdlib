------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition for the permutation relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Permutation.Propositional
  {a} {A : Set a} where

open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as EqReasoning

------------------------------------------------------------------------
-- An inductive definition of permutation

-- Note that one would expect that this would be defined in terms of
-- `Permutation.Setoid`. This is not currently the case as it involves
-- adding in a bunch of trivial `_≡_` proofs to the constructors which
-- a) adds noise and b) prevents easy access to the variables `x`, `y`.
-- This may be changed in future when a better solution is found.

infix 3 _↭_

data _↭_ : Rel (List A) a where
  refl  : ∀ {xs}        → xs ↭ xs
  prep  : ∀ {xs ys} x   → xs ↭ ys → x ∷ xs ↭ x ∷ ys
  swap  : ∀ {xs ys} x y → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
  trans : ∀ {xs ys zs}  → xs ↭ ys → ys ↭ zs → xs ↭ zs

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive refl = refl

↭-refl : Reflexive _↭_
↭-refl = refl

↭-sym : ∀ {xs ys} → xs ↭ ys → ys ↭ xs
↭-sym refl                = refl
↭-sym (prep x xs↭ys)      = prep x (↭-sym xs↭ys)
↭-sym (swap x y xs↭ys)    = swap y x (↭-sym xs↭ys)
↭-sym (trans xs↭ys ys↭zs) = trans (↭-sym ys↭zs) (↭-sym xs↭ys)

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
