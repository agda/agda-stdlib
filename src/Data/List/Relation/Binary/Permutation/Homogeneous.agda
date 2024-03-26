------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Homogeneous where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; []; _∷_)
open import Data.Nat.Base using (ℕ; suc; _+_; _<_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel; _⇒_)

private
  variable
    a r s : Level
    A : Set a
    xs ys zs : List A
    x y x′ y′ : A


------------------------------------------------------------------------
-- Definition

module _ {A : Set a} (R : Rel A r) where

  data Permutation : Rel (List A) (a ⊔ r) where
    refl  : Pointwise R xs ys → Permutation xs ys
    prep  : (eq : R x y) → Permutation xs ys → Permutation (x ∷ xs) (y ∷ ys)
    swap  : (eq₁ : R x x′) (eq₂ : R y y′) → Permutation xs ys →
            Permutation (x ∷ y ∷ xs) (y′ ∷ x′ ∷ ys)
    trans : Permutation xs ys → Permutation ys zs → Permutation xs zs

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
