------------------------------------------------------------------------
-- The Agda standard library
--
-- Maps from keys to values, based on AVL trees
-- This modules provides a simpler map interface, without a dependency
-- between the key and value types.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.AVL.Map
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (Maybe)
open import Data.Product using (_×_)
open import Level using (_⊔_)

import Data.AVL strictTotalOrder as AVL
open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)

------------------------------------------------------------------------
-- The map type

Map : ∀ {v} → (V : Set v) → Set (a ⊔ v ⊔ ℓ₂)
Map v = AVL.Tree (AVL.const v)

------------------------------------------------------------------------
-- Repackaged functions

module _ {v} {V : Set v} where

  empty : Map V
  empty = AVL.empty

  singleton : Key → V → Map V
  singleton = AVL.singleton

  insert : Key → V → Map V → Map V
  insert = AVL.insert

  insertWith : Key → (Maybe V → V) → Map V → Map V
  insertWith = AVL.insertWith

  delete : Key → Map V → Map V
  delete = AVL.delete

  lookup : Key → Map V → Maybe V
  lookup = AVL.lookup

module _ {v w} {V : Set v} {W : Set w} where

  map : (V → W) → Map V → Map W
  map f = AVL.map f

module _ {v} {V : Set v} where

  infix 4 _∈?_

  _∈?_ : Key → Map V → Bool
  _∈?_ = AVL._∈?_

  headTail : Map V → Maybe ((Key × V) × Map V)
  headTail = AVL.headTail

  initLast : Map V → Maybe (Map V × (Key × V))
  initLast = AVL.initLast

  fromList : List (Key × V) → Map V
  fromList = AVL.fromList

  toList : Map V → List (Key × V)
  toList = AVL.toList

module _ {v w} {V : Set v} {W : Set w} where

  unionWith : (V → Maybe W → W) →
              Map V → Map W → Map W
  unionWith f = AVL.unionWith f

module _ {v} {V : Set v} where

  union : Map V → Map V → Map V
  union = AVL.union

  unionsWith : (V → Maybe V → V) → List (Map V) → Map V
  unionsWith f = AVL.unionsWith f

  unions : List (Map V) → Map V
  unions = AVL.unions
