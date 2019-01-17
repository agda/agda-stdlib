------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition for the permutation relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Permutation.Inductive {a} {A : Set a} where

open import Data.List using (List; []; _∷_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as EqReasoning

------------------------------------------------------------------------
-- An inductive definition of permutation

infix 3 _↭_

data _↭_ : Rel (List A) a where
  refl  : ∀ {xs}        → xs ↭ xs
  prep  : ∀ {xs ys} x   → xs ↭ ys → x ∷ xs ↭ x ∷ ys
  swap  : ∀ {xs ys} x y → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
  trans : ∀ {xs ys zs}  → xs ↭ ys → ys ↭ zs → xs ↭ zs

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive refl = refl

↭-refl : Reflexive _↭_
↭-refl = refl

↭-sym : ∀ {xs ys} → xs ↭ ys → ys ↭ xs
↭-sym refl                = refl
↭-sym (prep x xs↭ys)      = prep x (↭-sym xs↭ys)
↭-sym (swap x y xs↭ys)    = swap y x (↭-sym xs↭ys)
↭-sym (trans xs↭ys ys↭zs) = trans (↭-sym ys↭zs) (↭-sym xs↭ys)

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
-- A reasoning API to chain permutation proofs and allow "zooming in"
-- to localised reasoning.

module PermutationReasoning where

  open EqReasoning ↭-setoid
    using (_IsRelatedTo_; relTo)

  open EqReasoning ↭-setoid public
    using (begin_ ; _∎ ; _≡⟨⟩_; _≡⟨_⟩_)
    renaming (_≈⟨_⟩_ to _↭⟨_⟩_)

  infixr 2 _∷_<⟨_⟩_  _∷_∷_<<⟨_⟩_

  -- Skip reasoning on the first element
  _∷_<⟨_⟩_ : ∀ x xs {ys zs : List A} → xs ↭ ys →
               (x ∷ ys) IsRelatedTo zs → (x ∷ xs) IsRelatedTo zs
  x ∷ xs <⟨ xs↭ys ⟩ rel = relTo (trans (prep x xs↭ys) (begin rel))

  -- Skip reasoning about the first two elements
  _∷_∷_<<⟨_⟩_ : ∀ x y xs {ys zs : List A} → xs ↭ ys →
                  (y ∷ x ∷ ys) IsRelatedTo zs → (x ∷ y ∷ xs) IsRelatedTo zs
  x ∷ y ∷ xs <<⟨ xs↭ys ⟩ rel = relTo (trans (swap x y xs↭ys) (begin rel))
