------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty AVL trees, where equality for keys is propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; IsStrictTotalOrder; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Data.AVL.NonEmpty.Propositional
  {k r} {Key : Set k} {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

open import Level

private strictTotalOrder = record { isStrictTotalOrder = isStrictTotalOrder}
open import Data.AVL.Value (StrictTotalOrder.Eq.setoid strictTotalOrder)
import Data.AVL.NonEmpty strictTotalOrder as AVL⁺

Tree⁺ : ∀ {v} (V : Key → Set v) → Set (k ⊔ v ⊔ r)
Tree⁺ V = AVL⁺.Tree⁺ λ where
  .Value.family          → V
  .Value.respects refl t → t

open AVL⁺ hiding (Tree⁺) public
