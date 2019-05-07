------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List using (List; _∷_)
open import Level using (Level; _⊔_)
open import Relation.Binary

module Data.List.Relation.Binary.Permutation.Homogeneous where

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
-- _↭_ is an equivalence

Perm-refl : ∀ {R : Rel A r} → Reflexive (Permutation R)
Perm-refl = refl

Perm-trans : ∀ {R : Rel A r} → Transitive (Permutation R)
Perm-trans = trans

module _ {R : Rel A r} (R-sym : Symmetric R) where

  Perm-sym : Symmetric (Permutation R)
  Perm-sym refl                   = refl
  Perm-sym (prep x∼x' xs↭ys)      = prep (R-sym x∼x') (Perm-sym xs↭ys)
  Perm-sym (swap x∼x' y∼y' xs↭ys) = swap (R-sym y∼y') (R-sym x∼x') (Perm-sym xs↭ys)
  Perm-sym (trans xs↭ys ys↭zs)    = trans (Perm-sym ys↭zs) (Perm-sym xs↭ys)

  Perm-isEquivalence : IsEquivalence (Permutation R)
  Perm-isEquivalence = record
    { refl  = Perm-refl
    ; sym   = Perm-sym
    ; trans = Perm-trans
    }

  Perm-setoid : Setoid _ _
  Perm-setoid = record
    { isEquivalence = Perm-isEquivalence
    }

map : ∀ {R : Rel A r} {S : Rel A s} →
      (R ⇒ S) → (Permutation R ⇒ Permutation S)
map R⇒S refl = refl
map R⇒S (prep eq xs∼ys) = prep (R⇒S eq) (map R⇒S xs∼ys)
map R⇒S (swap eq₁ eq₂ xs∼ys) = swap (R⇒S eq₁) (R⇒S eq₂) (map R⇒S xs∼ys)
map R⇒S (trans xs∼ys ys∼zs) = trans (map R⇒S xs∼ys) (map R⇒S ys∼zs)
