------------------------------------------------------------------------
-- The Agda standard library
--
-- Some code related to indexed AVL trees that relies on the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Data.AVL.Indexed.WithK
       {k r} (Key : Set k) {_<_ : Rel Key r}
       (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

open import Data.Product

open import Data.AVL.Indexed Key isStrictTotalOrder

module _ {v} {V : Key → Set v} where

  node-injectiveˡ : ∀ {hˡ hʳ h l u k}
    {lk₁ : Tree V l [ proj₁ k ] hˡ} {lk₂ : Tree V l [ proj₁ k ] hˡ}
    {ku₁ : Tree V [ proj₁ k ] u hʳ} {ku₂ : Tree V [ proj₁ k ] u hʳ}
    {bal₁ bal₂ : hˡ ∼ hʳ ⊔ h} →
    node k lk₁ ku₁ bal₁ ≡ node k lk₂ ku₂ bal₂ → lk₁ ≡ lk₂
  node-injectiveˡ refl = refl

  node-injectiveʳ : ∀ {hˡ hʳ h l u k}
    {lk₁ : Tree V l [ proj₁ k ] hˡ} {lk₂ : Tree V l [ proj₁ k ] hˡ}
    {ku₁ : Tree V [ proj₁ k ] u hʳ} {ku₂ : Tree V [ proj₁ k ] u hʳ}
    {bal₁ bal₂ : hˡ ∼ hʳ ⊔ h} →
    node k lk₁ ku₁ bal₁ ≡ node k lk₂ ku₂ bal₂ → ku₁ ≡ ku₂
  node-injectiveʳ refl = refl

  node-injective-bal : ∀ {hˡ hʳ h l u k}
    {lk₁ : Tree V l [ proj₁ k ] hˡ} {lk₂ : Tree V l [ proj₁ k ] hˡ}
    {ku₁ : Tree V [ proj₁ k ] u hʳ} {ku₂ : Tree V [ proj₁ k ] u hʳ}
    {bal₁ bal₂ : hˡ ∼ hʳ ⊔ h} →
    node k lk₁ ku₁ bal₁ ≡ node k lk₂ ku₂ bal₂ → bal₁ ≡ bal₂
  node-injective-bal refl = refl
