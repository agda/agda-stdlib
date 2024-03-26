------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Homogeneous where

open import Data.List.Base as List using (List; []; _∷_; [_]; _++_; length)
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.Nat.Base using (ℕ; suc; _+_; _<_)
open import Data.Nat.Properties
open import Data.Product.Base using (_,_; _×_; ∃; ∃₂)
open import Function.Base using (_∘_; flip)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel; _⇒_; _Preserves_⟶_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Structures using (IsEquivalence; IsPartialEquivalence)
open import Relation.Binary.Definitions
  using ( Reflexive; Symmetric; Transitive; LeftTrans; RightTrans
        ; _Respects_; _Respects₂_; _Respectsˡ_; _Respectsʳ_)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_ ; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no; does)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred; Decidable)

private
  variable
    a p r s : Level
    A B : Set a
    xs ys zs : List A
    x y z v w : A


------------------------------------------------------------------------
-- Definition

module _ {A : Set a} (R : Rel A r) where

  data Permutation : Rel (List A) (a ⊔ r) where
    refl  : ∀ {xs ys} → Pointwise R xs ys → Permutation xs ys
    prep  : ∀ {xs ys x y} (eq : R x y) → Permutation xs ys → Permutation (x ∷ xs) (y ∷ ys)
    swap  : ∀ {xs ys x y x′ y′} (eq₁ : R x x′) (eq₂ : R y y′) →
            Permutation xs ys → Permutation (x ∷ y ∷ xs) (y′ ∷ x′ ∷ ys)
    trans : Transitive Permutation

------------------------------------------------------------------------
-- Map

module _ {R : Rel A r} {S : Rel A s} where

  map : (R ⇒ S) → (Permutation R ⇒ Permutation S)
  map R⇒S (refl xs∼ys)         = refl (Pointwise.map R⇒S xs∼ys)
  map R⇒S (prep e xs∼ys)       = prep (R⇒S e) (map R⇒S xs∼ys)
  map R⇒S (swap e₁ e₂ xs∼ys)   = swap (R⇒S e₁) (R⇒S e₂) (map R⇒S xs∼ys)
  map R⇒S (trans xs∼ys ys∼zs)  = trans (map R⇒S xs∼ys) (map R⇒S ys∼zs)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.1

steps : {R : Rel A r} → Permutation R xs ys → ℕ
steps (refl _)            = 1
steps (prep _ xs↭ys)      = suc (steps xs↭ys)
steps (swap _ _ xs↭ys)    = suc (steps xs↭ys)
steps (trans xs↭ys ys↭zs) = steps xs↭ys + steps ys↭zs

{-# WARNING_ON_USAGE steps
"Warning: steps was deprecated in v2.1."
#-}
