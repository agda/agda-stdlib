------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Permutation.Homogeneous where

open import Data.List using (List; _∷_)
open import Level using (Level; _⊔_)
open import Relation.Binary

private
  variable
    a r s : Level
    A : Set a

data Permutation {A : Set a} (R : Rel A r) : Rel (List A) (a ⊔ r) where
  refl  : ∀ {xs} → Permutation R xs xs
  prep  : ∀ {xs ys x y} (eq : R x y) → Permutation R xs ys → Permutation R (x ∷ xs) (y ∷ ys)
  swap  : ∀ {xs ys x y x' y'} (eq₁ : R x x') (eq₂ : R y y') → Permutation R xs ys → Permutation R (x ∷ y ∷ xs) (y' ∷ x' ∷ ys)
  trans : ∀ {xs ys zs} → Permutation R xs ys → Permutation R ys zs → Permutation R xs zs

------------------------------------------------------------------------
-- The Permutation relation is an equivalence

module _ {R : Rel A r}  where

  sym : Symmetric R → Symmetric (Permutation R)
  sym R-sym refl                   = refl
  sym R-sym (prep x∼x' xs↭ys)      = prep (R-sym x∼x') (sym R-sym xs↭ys)
  sym R-sym (swap x∼x' y∼y' xs↭ys) = swap (R-sym y∼y') (R-sym x∼x') (sym R-sym xs↭ys)
  sym R-sym (trans xs↭ys ys↭zs)    = trans (sym R-sym ys↭zs) (sym R-sym xs↭ys)

  isPartialEquivalence : Symmetric R → IsPartialEquivalence (Permutation R)
  isPartialEquivalence R-sym = record
    { sym   = sym R-sym
    ; trans = trans
    }

  isEquivalence : Symmetric R → IsEquivalence (Permutation R)
  isEquivalence R-sym = record
    { refl  = refl
    ; isPartialEquivalence = isPartialEquivalence R-sym
    }

  setoid : Symmetric R → Setoid _ _
  setoid R-sym = record
    { isEquivalence = isEquivalence R-sym
    }

map : ∀ {R : Rel A r} {S : Rel A s} →
      (R ⇒ S) → (Permutation R ⇒ Permutation S)
map R⇒S refl                 = refl
map R⇒S (prep e xs∼ys)       = prep (R⇒S e) (map R⇒S xs∼ys)
map R⇒S (swap e₁ e₂ xs∼ys)   = swap (R⇒S e₁) (R⇒S e₂) (map R⇒S xs∼ys)
map R⇒S (trans xs∼ys ys∼zs)  = trans (map R⇒S xs∼ys) (map R⇒S ys∼zs)
