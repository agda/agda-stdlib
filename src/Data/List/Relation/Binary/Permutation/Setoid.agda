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

module Data.List.Relation.Binary.Permutation.Setoid
  {b} {ℓ} (S : Setoid b ℓ) where

open Setoid S using (Carrier; _≈_; sym)

------------------------------------------------------------------------
-- A setoid equality definition of permutation

infix 3 _↭_

data _↭_ : Rel (List Carrier) (b ⊔ ℓ) where
  refl : ∀ {xs} → xs ↭ xs
  prep : ∀ {xs ys} {x} {x'} (eq : x ≈ x') → xs ↭ ys →
               x ∷ xs ↭ x' ∷ ys
  swap : ∀ {xs ys} {x} {y} {x'} {y'} (eq₁ : x ≈ x') (eq₂ : y ≈ y') →
               xs ↭ ys → x ∷ y ∷ xs ↭ y' ∷ x' ∷ ys
  trans : ∀ {xs ys zs} → xs ↭ ys → ys ↭ zs → xs ↭ zs

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-refl : Reflexive _↭_
↭-refl = refl

↭-sym : Symmetric _↭_
↭-sym refl                 = refl
↭-sym (prep eq xs↭ys)      = prep (sym eq) (↭-sym xs↭ys)
↭-sym (swap eq₁ eq₂ xs↭ys) = swap (sym eq₂) (sym eq₁) (↭-sym xs↭ys)
↭-sym (trans p p₁)         = trans (↭-sym p₁) (↭-sym p)

↭-trans : Transitive _↭_
↭-trans = trans

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = record
  { refl  = refl
  ; sym   = ↭-sym
  ; trans = trans
  }

↭-setoid : Setoid _ _
↭-setoid = record
  { isEquivalence = ↭-isEquivalence
  }

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs

module PermutationReasoning where

  open EqReasoning ↭-setoid public
    using (begin_ ; _∎ ; _≡⟨⟩_; _≡⟨_⟩_)
    renaming (_≈⟨_⟩_ to _↭⟨_⟩_)
