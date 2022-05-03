------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Permutation.Homogeneous where

open import Data.List.Base using (List; _∷_)
open import Level using (Level; _⊔_)
open import Relation.Binary

private
  variable
    a pr r ps s : Level
    A : Set a

-- PR is morally the pointwise lifting of R to lists but it need not be intensionally
data Permutation {A : Set a} (PR : Rel (List A) pr) (R : Rel A r) : Rel (List A) (a ⊔ pr ⊔ r) where
  refl  : ∀ {xs ys} → PR xs ys → Permutation PR R xs ys
  prep  : ∀ {xs ys x y} (eq : R x y) → Permutation PR R xs ys → Permutation PR R (x ∷ xs) (y ∷ ys)
  swap  : ∀ {xs ys x y x′ y′} (eq₁ : R x x′) (eq₂ : R y y′) → Permutation PR R xs ys → Permutation PR R (x ∷ y ∷ xs) (y′ ∷ x′ ∷ ys)
  trans : ∀ {xs ys zs} → Permutation PR R xs ys → Permutation PR R ys zs → Permutation PR R xs zs

------------------------------------------------------------------------
-- The Permutation relation is an equivalence

module _ {PR : Rel (List A) pr} {R : Rel A r}  where

  sym : Symmetric PR → Symmetric R → Symmetric (Permutation PR R)
  sym PR-sym R-sym (refl xs∼ys)           = refl (PR-sym xs∼ys)
  sym PR-sym R-sym (prep x∼x′ xs↭ys)      = prep (R-sym x∼x′) (sym PR-sym R-sym xs↭ys)
  sym PR-sym R-sym (swap x∼x′ y∼y′ xs↭ys) = swap (R-sym y∼y′) (R-sym x∼x′) (sym PR-sym R-sym xs↭ys)
  sym PR-sym R-sym (trans xs↭ys ys↭zs)    = trans (sym PR-sym R-sym ys↭zs) (sym PR-sym R-sym xs↭ys)

  isEquivalence : Reflexive PR →
                  Symmetric PR → Symmetric R →
                  IsEquivalence (Permutation PR R)
  isEquivalence PR-refl PR-sym R-sym = record
    { refl  = refl PR-refl
    ; sym   = sym PR-sym R-sym
    ; trans = trans
    }

  setoid : Reflexive PR → Symmetric PR → Symmetric R → Setoid _ _
  setoid PR-refl PR-sym R-sym = record
    { isEquivalence = isEquivalence PR-refl PR-sym R-sym
    }

map : ∀ {PR : Rel (List A) pr} {PS : Rel (List A) ps} →
        {R : Rel A r} {S : Rel A s} →
        (PR ⇒ PS) → (R ⇒ S) → (Permutation PR R ⇒ Permutation PS S)
map PR⇒PS R⇒S (refl xs∼ys)         = refl (PR⇒PS xs∼ys)
map PR⇒PS R⇒S (prep e xs∼ys)       = prep (R⇒S e) (map PR⇒PS R⇒S xs∼ys)
map PR⇒PS R⇒S (swap e₁ e₂ xs∼ys)   = swap (R⇒S e₁) (R⇒S e₂) (map PR⇒PS R⇒S xs∼ys)
map PR⇒PS R⇒S (trans xs∼ys ys∼zs)  = trans (map PR⇒PS R⇒S xs∼ys) (map PR⇒PS R⇒S ys∼zs)
