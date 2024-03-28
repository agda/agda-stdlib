------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Function.Base using (_∘′_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; LeftTrans; RightTrans)
open import Relation.Binary.Reasoning.Syntax

module Data.List.Relation.Binary.Permutation.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open import Data.List.Base using (List; _∷_)
import Data.List.Relation.Binary.Permutation.Homogeneous as Homogeneous
import Data.List.Relation.Binary.Pointwise.Properties as Pointwise using (refl)
open import Data.List.Relation.Binary.Equality.Setoid S
open import Data.Nat.Base using (ℕ)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open module ≈ = Setoid S using (_≈_) renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition

open Homogeneous public
  using (refl; prep; swap; trans)

infix 3 _↭_

_↭_ : Rel (List A) (a ⊔ ℓ)
_↭_ = Homogeneous.Permutation _≈_

------------------------------------------------------------------------
-- Constructor aliases

-- Constructor alias

↭-pointwise : _≋_ ⇒ _↭_
↭-pointwise = refl

-- These provide aliases for `swap` and `prep` when the elements being
-- swapped or prepended are propositionally equal

↭-prep : ∀ x {xs ys} → xs ↭ ys → x ∷ xs ↭ x ∷ ys
↭-prep x xs↭ys = prep ≈.refl xs↭ys

↭-swap : ∀ x y {xs ys} → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
↭-swap x y xs↭ys = swap ≈.refl ≈.refl xs↭ys

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive refl = ↭-pointwise ≋-refl

↭-refl : Reflexive _↭_
↭-refl = ↭-reflexive refl

↭-sym : Symmetric _↭_
↭-sym = Homogeneous.sym ≈.sym

↭-transˡ-≋ : LeftTrans _≋_ _↭_
↭-transˡ-≋ xs≋ys               (refl ys≋zs)
  = refl (≋-trans xs≋ys ys≋zs)
↭-transˡ-≋ (x≈y ∷ xs≋ys)       (prep y≈z ys↭zs)
  = prep (≈.trans x≈y y≈z) (↭-transˡ-≋ xs≋ys ys↭zs)
↭-transˡ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ ys↭zs)
  = swap (≈.trans x≈y eq₁) (≈.trans w≈z eq₂) (↭-transˡ-≋ xs≋ys ys↭zs)
↭-transˡ-≋ xs≋ys               (trans ys↭ws ws↭zs)
  = trans (↭-transˡ-≋ xs≋ys ys↭ws) ws↭zs

↭-transʳ-≋ : RightTrans _↭_ _≋_
↭-transʳ-≋ (refl xs≋ys)         ys≋zs
  = refl (≋-trans xs≋ys ys≋zs)
↭-transʳ-≋ (prep x≈y xs↭ys)     (y≈z ∷ ys≋zs)
  = prep (≈.trans x≈y y≈z) (↭-transʳ-≋ xs↭ys ys≋zs)
↭-transʳ-≋ (swap eq₁ eq₂ xs↭ys) (x≈w ∷ y≈z ∷ ys≋zs)
  = swap (≈.trans eq₁ y≈z) (≈.trans eq₂ x≈w) (↭-transʳ-≋ xs↭ys ys≋zs)
↭-transʳ-≋ (trans xs↭ws ws↭ys)  ys≋zs
  = trans xs↭ws (↭-transʳ-≋ ws↭ys ys≋zs)

↭-trans : Transitive _↭_
↭-trans (refl xs≋ys) ys↭zs = ↭-transˡ-≋ xs≋ys ys↭zs
↭-trans xs↭ys (refl ys≋zs) = ↭-transʳ-≋ xs↭ys ys≋zs
↭-trans xs↭ys ys↭zs        = trans xs↭ys ys↭zs

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = record
    { refl  = ↭-refl
    ; sym   = ↭-sym
    ; trans = ↭-trans
    }

↭-setoid : Setoid _ _
↭-setoid = record { isEquivalence = ↭-isEquivalence }

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs

module PermutationReasoning where

  private module Base = ≈-Reasoning ↭-setoid

  open Base public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)
    renaming (≈-go to ↭-go)

  open ↭-syntax _IsRelatedTo_ _IsRelatedTo_ ↭-go ↭-sym public
  open ≋-syntax _IsRelatedTo_ _IsRelatedTo_ (↭-go ∘′ ↭-pointwise) ≋-sym public

  -- Some extra combinators that allow us to skip certain elements

  infixr 2 step-swap step-prep

  -- Skip reasoning on the first element
  step-prep : ∀ x xs {ys zs : List A} → (x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ xs) IsRelatedTo zs
  step-prep x xs rel xs↭ys = ↭-go (↭-prep x xs↭ys) rel

  -- Skip reasoning about the first two elements
  step-swap : ∀ x y xs {ys zs : List A} → (y ∷ x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ y ∷ xs) IsRelatedTo zs
  step-swap x y xs rel xs↭ys = ↭-go (↭-swap x y xs↭ys) rel

  syntax step-prep x xs y↭z x↭y = x ∷ xs <⟨ x↭y ⟩ y↭z
  syntax step-swap x y xs y↭z x↭y = x ∷ y ∷ xs <<⟨ x↭y ⟩ y↭z

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.1

steps : ∀ {xs ys} → xs ↭ ys → ℕ
steps = Homogeneous.steps
{-# WARNING_ON_USAGE steps
"Warning: steps was deprecated in v2.1.
Please use Homogeneous.steps explicitly instead."
#-}

