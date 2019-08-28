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
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_)
open import Level using (_⊔_)

import Data.AVL strictTotalOrder as AVL
open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)

------------------------------------------------------------------------
-- The map type

Map : ∀ {i} → (v : Set i) → Set (a ⊔ i ⊔ ℓ₂)
Map v = AVL.Tree (AVL.const v)

------------------------------------------------------------------------
-- Repackaged functions

module _ {i} {v : Set i} where

  empty : Map v
  empty = AVL.empty

  singleton : Key → v → Map v
  singleton = AVL.singleton

  insert : Key → v → Map v → Map v
  insert = AVL.insert

  insertWith : Key → (Maybe v → v) → Map v → Map v
  insertWith = AVL.insertWith

  delete : Key → Map v → Map v
  delete = AVL.delete

  lookup : Key → Map v → Maybe v
  lookup = AVL.lookup

module _ {i j} {v : Set i} {w : Set j} where

  map : (v → w) → Map v → Map w
  map f = AVL.map f

module _ {i} {v : Set i} where

  infix 4 _∈?_

  _∈?_ : Key → Map v → Bool
  _∈?_ = AVL._∈?_

  headTail : Map v → Maybe ((Key × v) × Map v)
  headTail = AVL.headTail

  initLast : Map v → Maybe (Map v × (Key × v))
  initLast = AVL.initLast

  fromList : List (Key × v) → Map v
  fromList = AVL.fromList

  toList : Map v → List (Key × v)
  toList = AVL.toList

module _ {i j} {v : Set i} {w : Set j} where

  unionWith : (v → Maybe w → w) →
              Map v → Map w → Map w
  unionWith f = AVL.unionWith f

module _ {i} {v : Set i} where

  union : Map v → Map v → Map v
  union = AVL.union

  unionsWith : (v → Maybe v → v) → List (Map v) → Map v
  unionsWith f = AVL.unionsWith f

  unions : List (Map v) → Map v
  unions = AVL.unions
