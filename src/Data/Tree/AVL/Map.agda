------------------------------------------------------------------------
-- The Agda standard library
--
-- Maps from keys to values, based on AVL trees
-- This modules provides a simpler map interface, without a dependency
-- between the key and value types.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Map
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (Bool)
open import Data.List.Base as List using (List)
open import Data.Maybe.Base as Maybe using (Maybe)
open import Data.Nat.Base using (ℕ)
open import Data.Product as Prod using (_×_)
open import Function.Base using (_∘′_)
open import Level using (Level; _⊔_)

private
  variable
    l v w x : Level
    A : Set l
    V : Set v
    W : Set w
    X : Set x

import Data.Tree.AVL strictTotalOrder as AVL
open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)

------------------------------------------------------------------------
-- The map type

Map : (V : Set v) → Set (a ⊔ v ⊔ ℓ₂)
Map V = AVL.Tree (AVL.const V)

------------------------------------------------------------------------
-- Repackaged functions

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

map : (V → W) → Map V → Map W
map f = AVL.map f

infix 4 _∈?_
_∈?_ : Key → Map V → Bool
_∈?_ = AVL._∈?_

headTail : Map V → Maybe ((Key × V) × Map V)
headTail = Maybe.map (Prod.map₁ AVL.toPair) ∘′ AVL.headTail

initLast : Map V → Maybe (Map V × (Key × V))
initLast = Maybe.map (Prod.map₂ AVL.toPair) ∘′ AVL.initLast

foldr : (Key → V → A → A) → A → Map V → A
foldr cons = AVL.foldr (λ {k} → cons k)

fromList : List (Key × V) → Map V
fromList = AVL.fromList ∘′ List.map AVL.fromPair

toList : Map V → List (Key × V)
toList = List.map AVL.toPair ∘′ AVL.toList

size : Map V → ℕ
size = AVL.size

------------------------------------------------------------------------
-- Naïve implementations of union

unionWith : (V → Maybe W → W) →
            Map V → Map W → Map W
unionWith f = AVL.unionWith f

union : Map V → Map V → Map V
union = AVL.union

unionsWith : (V → Maybe V → V) → List (Map V) → Map V
unionsWith f = AVL.unionsWith f

unions : List (Map V) → Map V
unions = AVL.unions

------------------------------------------------------------------------
-- Naïve implementations of intersection

intersectionWith : (V → W → X) → Map V → Map W → Map X
intersectionWith f = AVL.intersectionWith f

intersection : Map V → Map V → Map V
intersection = AVL.intersection

intersectionsWith : (V → V → V) → List (Map V) → Map V
intersectionsWith f = AVL.intersectionsWith f

intersections : List (Map V) → Map V
intersections = AVL.intersections
