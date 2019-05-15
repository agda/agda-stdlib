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

data Permutation (R : Rel {a} A r) : Rel (List A) (a ⊔ r) where
  refl : ∀ {xs} → Permutation R xs xs
  prep : ∀ {xs ys} {x} {x'} (eq : R x x') → Permutation R xs ys →
               Permutation R (x ∷ xs) (x' ∷ ys)
  swap : ∀ {xs ys} {x} {y} {x'} {y'} (eq₁ : R x x') (eq₂ : R y y') →
               Permutation R xs ys → Permutation R (x ∷ y ∷ xs) (y' ∷ x' ∷ ys)
  trans : ∀ {xs ys zs} → Permutation R xs ys → Permutation R ys zs → Permutation R xs zs

------------------------------------------------------------------------
-- The Permutation relation is an equivalence

module _ {R : Rel A r} (R-sym : Symmetric R) where

  sym : Symmetric (Permutation R)
  sym refl                   = refl
  sym (prep x∼x' xs↭ys)      = prep (R-sym x∼x') (sym xs↭ys)
  sym (swap x∼x' y∼y' xs↭ys) = swap (R-sym y∼y') (R-sym x∼x') (sym xs↭ys)
  sym (trans xs↭ys ys↭zs)    = trans (sym ys↭zs) (sym xs↭ys)

  isEquivalence : IsEquivalence (Permutation R)
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  setoid : Setoid _ _
  setoid = record
    { isEquivalence = isEquivalence
    }

map : ∀ {R : Rel A r} {S : Rel A s} →
      (R ⇒ S) → (Permutation R ⇒ Permutation S)
map R⇒S refl = refl
map R⇒S (prep eq xs∼ys) = prep (R⇒S eq) (map R⇒S xs∼ys)
map R⇒S (swap eq₁ eq₂ xs∼ys) = swap (R⇒S eq₁) (R⇒S eq₂) (map R⇒S xs∼ys)
map R⇒S (trans xs∼ys ys∼zs) = trans (map R⇒S xs∼ys) (map R⇒S ys∼zs)
