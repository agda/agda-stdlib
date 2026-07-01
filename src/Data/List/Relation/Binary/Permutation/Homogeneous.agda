------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Permutation.Homogeneous where

open import Data.List.Base using (List; _∷_; length)
open import Data.List.Relation.Binary.Pointwise.Base as Pointwise
  using (Pointwise)
import Data.List.Relation.Binary.Pointwise.Properties as Pointwise
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Fin.Base using (Fin; zero; suc; cast)
import Data.Fin.Permutation as Fin
open import Level using (Level; _⊔_)
open import Function.Base using (_∘_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Symmetric)

private
  variable
    a r s : Level
    A : Set a
    R S : Rel A r

data Permutation {A : Set a} (R : Rel A r) : Rel (List A) (a ⊔ r) where
  refl  : ∀ {xs ys} → Pointwise R xs ys → Permutation R xs ys
  prep  : ∀ {xs ys x y} (eq : R x y) → Permutation R xs ys → Permutation R (x ∷ xs) (y ∷ ys)
  swap  : ∀ {xs ys x y x′ y′} (eq₁ : R x x′) (eq₂ : R y y′) → Permutation R xs ys → Permutation R (x ∷ y ∷ xs) (y′ ∷ x′ ∷ ys)
  trans : ∀ {xs ys zs} → Permutation R xs ys → Permutation R ys zs → Permutation R xs zs

------------------------------------------------------------------------
-- The Permutation relation is an equivalence

sym : Symmetric R → Symmetric (Permutation R)
sym R-sym (refl xs∼ys)           = refl (Pointwise.symmetric R-sym xs∼ys)
sym R-sym (prep x∼x′ xs↭ys)      = prep (R-sym x∼x′) (sym R-sym xs↭ys)
sym R-sym (swap x∼x′ y∼y′ xs↭ys) = swap (R-sym y∼y′) (R-sym x∼x′) (sym R-sym xs↭ys)
sym R-sym (trans xs↭ys ys↭zs)    = trans (sym R-sym ys↭zs) (sym R-sym xs↭ys)

isEquivalence : Reflexive R → Symmetric R → IsEquivalence (Permutation R)
isEquivalence R-refl R-sym = record
  { refl  = refl (Pointwise.refl R-refl)
  ; sym   = sym R-sym
  ; trans = trans
  }

setoid : Reflexive R → Symmetric R → Setoid _ _
setoid {R = R} R-refl R-sym = record
  { isEquivalence = isEquivalence {R = R} R-refl R-sym
  }

map : (R ⇒ S) → (Permutation R ⇒ Permutation S)
map R⇒S (refl xs∼ys)         = refl (Pointwise.map R⇒S xs∼ys)
map R⇒S (prep e xs∼ys)       = prep (R⇒S e) (map R⇒S xs∼ys)
map R⇒S (swap e₁ e₂ xs∼ys)   = swap (R⇒S e₁) (R⇒S e₂) (map R⇒S xs∼ys)
map R⇒S (trans xs∼ys ys∼zs)  = trans (map R⇒S xs∼ys) (map R⇒S ys∼zs)

-- Measures the number of constructors, can be useful for termination proofs
steps : ∀ {xs ys} → Permutation R xs ys → ℕ
steps (refl _)            = 1
steps (prep _ xs↭ys)      = suc (steps xs↭ys)
steps (swap _ _ xs↭ys)    = suc (steps xs↭ys)
steps (trans xs↭ys ys↭zs) = steps xs↭ys + steps ys↭zs

onIndices : ∀ {xs ys} → Permutation R xs ys → Fin.Permutation (length xs) (length ys)
onIndices (refl ≋)          = Fin.cast-id (Pointwise.Pointwise-length ≋)
onIndices (prep e xs↭ys)   = Fin.lift₀ (onIndices xs↭ys)
onIndices (swap e f xs↭ys) = Fin.swap (onIndices xs↭ys)
onIndices (trans ↭₁ ↭₂)   = onIndices ↭₁ Fin.∘ₚ onIndices ↭₂
