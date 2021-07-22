------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive lists where all elements satisfy a predicate
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module Codata.Musical.Colist.Relation.Unary.All.Properties where

open import Codata.Musical.Colist.Base
open import Codata.Musical.Colist.Relation.Unary.All
open import Codata.Musical.Notation
open import Function.Base using (_∋_)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Unary using (Pred)

private
  variable
    a b p : Level
    A : Set a
    B : Set b
    P : Pred A p

∷-injectiveˡ : ∀ {x xs px qx pxs qxs} →
               (All P (x ∷ xs) ∋ px ∷ pxs) ≡ qx ∷ qxs → px ≡ qx
∷-injectiveˡ refl = refl

∷-injectiveʳ : ∀ {x xs px qx pxs qxs} →
               (All P (x ∷ xs) ∋ px ∷ pxs) ≡ qx ∷ qxs → pxs ≡ qxs
∷-injectiveʳ refl = refl
