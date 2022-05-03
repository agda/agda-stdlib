------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition for the permutation relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Propositional
  {a} {A : Set a} where

open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
import Data.List.Relation.Binary.Permutation.Homogeneous as Homogeneous
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Reasoning.Syntax


------------------------------------------------------------------------
-- Definition

infix 3 _↭_

_↭_ : Rel (List A) a
_↭_ = Homogeneous.Permutation _≡_ _≡_

pattern refl = Homogeneous.refl ≡.refl
pattern prep {xs} {ys} x tl = Homogeneous.prep {xs = xs} {ys = ys} {x = x} ≡.refl tl
pattern swap {xs} {ys} x y tl = Homogeneous.swap {xs = xs} {ys = ys} {x = x} {y = y} ≡.refl ≡.refl tl

open Homogeneous public
  using (trans)

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive ≡.refl = refl

↭-refl : Reflexive _↭_
↭-refl = refl

↭-sym : ∀ {xs ys} → xs ↭ ys → ys ↭ xs
↭-sym = Homogeneous.sym ≡.sym ≡.sym

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

  private module Base = ≈-Reasoning ↭-setoid

  open Base public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)
    renaming (≈-go to ↭-go)

  open ↭-syntax _IsRelatedTo_ _IsRelatedTo_ ↭-go ↭-sym public

  -- Some extra combinators that allow us to skip certain elements

  infixr 2 step-swap step-prep

  -- Skip reasoning on the first element
  step-prep : ∀ x xs {ys zs : List A} → (x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ xs) IsRelatedTo zs
  step-prep x xs rel xs↭ys = ↭-go (prep x xs↭ys) rel

  -- Skip reasoning about the first two elements
  step-swap : ∀ x y xs {ys zs : List A} → (y ∷ x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ y ∷ xs) IsRelatedTo zs
  step-swap x y xs rel xs↭ys = ↭-go (swap x y xs↭ys) rel

  syntax step-prep x xs y↭z x↭y = x ∷ xs <⟨ x↭y ⟩ y↭z
  syntax step-swap x y xs y↭z x↭y = x ∷ y ∷ xs <<⟨ x↭y ⟩ y↭z
