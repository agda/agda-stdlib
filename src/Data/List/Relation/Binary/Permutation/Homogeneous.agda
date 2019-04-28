------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List using (List; _∷_)
open import Level using (_⊔_)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqReasoning

module Data.List.Relation.Binary.Permutation.Homogeneous
  {a} {A} {ℓ} (_∼_ : Rel {a} A ℓ) where

------------------------------------------------------------------------
-- A setoid equality definition of permutation

infix 3 _↭_

data _↭_ : Rel (List A) (a ⊔ ℓ) where
  refl : ∀ {xs} → xs ↭ xs
  prep : ∀ {xs ys} {x} {x'} (eq : x ∼ x') → xs ↭ ys →
               x ∷ xs ↭ x' ∷ ys
  swap : ∀ {xs ys} {x} {y} {x'} {y'} (eq₁ : x ∼ x') (eq₂ : y ∼ y') →
               xs ↭ ys → x ∷ y ∷ xs ↭ y' ∷ x' ∷ ys
  trans : ∀ {xs ys zs} → xs ↭ ys → ys ↭ zs → xs ↭ zs

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-refl : Reflexive _↭_
↭-refl = refl

↭-trans : Transitive _↭_
↭-trans = trans

module _ (∼-sym : Symmetric _∼_) where

  ↭-sym : Symmetric _↭_
  ↭-sym refl                   = refl
  ↭-sym (prep x∼x' xs↭ys)      = prep (∼-sym x∼x') (↭-sym xs↭ys)
  ↭-sym (swap x∼x' y∼y' xs↭ys) = swap (∼-sym y∼y') (∼-sym x∼x') (↭-sym xs↭ys)
  ↭-sym (trans xs↭ys ys↭zs)    = trans (↭-sym ys↭zs) (↭-sym xs↭ys)

  ↭-isEquivalence : IsEquivalence _↭_
  ↭-isEquivalence = record
    { refl  = ↭-refl
    ; sym   = ↭-sym
    ; trans = ↭-trans
    }

  ↭-setoid : Setoid _ _
  ↭-setoid = record
    { isEquivalence = ↭-isEquivalence
    }

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs

module PermutationReasoning (∼-sym : Symmetric _∼_) where

  open EqReasoning (↭-setoid ∼-sym) public
    using (begin_ ; _∎ ; _≡⟨⟩_; _≡⟨_⟩_)
    renaming (_≈⟨_⟩_ to _↭⟨_⟩_)
