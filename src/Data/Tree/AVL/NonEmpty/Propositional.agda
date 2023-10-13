------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty AVL trees, where equality for keys is propositional equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)

module Data.Tree.AVL.NonEmpty.Propositional
  {k r} {Key : Set k} {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

open import Level

private
  strictTotalOrder : StrictTotalOrder _ _ _
  strictTotalOrder = record { isStrictTotalOrder = isStrictTotalOrder}
open import Data.Tree.AVL.Value (StrictTotalOrder.Eq.setoid strictTotalOrder)
import Data.Tree.AVL.NonEmpty strictTotalOrder as AVL⁺

Tree⁺ : ∀ {v} (V : Key → Set v) → Set (k ⊔ v ⊔ r)
Tree⁺ V = AVL⁺.Tree⁺ λ where
  .Value.family          → V
  .Value.respects refl t → t

open AVL⁺ hiding (Tree⁺) public
