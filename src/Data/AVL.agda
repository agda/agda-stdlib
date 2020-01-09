------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees
------------------------------------------------------------------------

-- AVL trees are balanced binary search trees.

-- The search tree invariant is specified using the technique
-- described by Conor McBride in his talk "Pivotal pragmatism".

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.AVL
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (Bool)
import Data.DifferenceList as DiffList
open import Data.List.Base as List using (List)
open import Data.Maybe using (Maybe; nothing; just; is-just)
open import Data.Nat.Base using (suc)
open import Data.Product hiding (map)
open import Function as F
open import Level using (_⊔_)
open import Relation.Unary

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
import Data.AVL.Indexed strictTotalOrder as Indexed
open Indexed using (K&_ ; ⊥⁺ ; ⊤⁺; ⊥⁺<⊤⁺; ⊥⁺<[_]<⊤⁺; ⊥⁺<[_]; [_]<⊤⁺)

------------------------------------------------------------------------
-- Re-export some core definitions publically

open Indexed using (Value; MkValue; const) public

------------------------------------------------------------------------
-- Types and functions with hidden indices

data Tree {v} (V : Value v) : Set (a ⊔ v ⊔ ℓ₂) where
  tree : ∀ {h} → Indexed.Tree V ⊥⁺ ⊤⁺ h → Tree V

module _ {v} {V : Value v} where

  private
    Val = Value.family V

  empty : Tree V
  empty = tree $′ Indexed.empty ⊥⁺<⊤⁺

  singleton : (k : Key) → Val k → Tree V
  singleton k v = tree (Indexed.singleton k v ⊥⁺<[ k ]<⊤⁺)

  insert : (k : Key) → Val k → Tree V → Tree V
  insert k v (tree t) = tree $′ proj₂ $ Indexed.insert k v t ⊥⁺<[ k ]<⊤⁺

  insertWith : (k : Key) → (Maybe (Val k) → Val k) →
               Tree V → Tree V
  insertWith k f (tree t) = tree $′ proj₂ $ Indexed.insertWith k f t ⊥⁺<[ k ]<⊤⁺

  delete : Key → Tree V → Tree V
  delete k (tree t) = tree $′ proj₂ $ Indexed.delete k t ⊥⁺<[ k ]<⊤⁺

  lookup : (k : Key) → Tree V → Maybe (Val k)
  lookup k (tree t) = Indexed.lookup k t ⊥⁺<[ k ]<⊤⁺

module _ {v w} {V : Value v} {W : Value w} where

  private
    Val = Value.family V
    Wal = Value.family W

  map : ∀[ Val ⇒ Wal ] → Tree V → Tree W
  map f (tree t) = tree $ Indexed.map f t

module _ {v} {V : Value v} where

  private
    Val = Value.family V


  infix 4 _∈?_

  _∈?_ : Key → Tree V → Bool
  k ∈? t = is-just (lookup k t)

  headTail : Tree V → Maybe ((K& V) × Tree V)
  headTail (tree (Indexed.leaf _)) = nothing
  headTail (tree {h = suc _} t)    with Indexed.headTail t
  ... | (k , _ , _ , t′) = just (k , tree (Indexed.castˡ ⊥⁺<[ _ ] t′))

  initLast : Tree V → Maybe (Tree V × (K& V))
  initLast (tree (Indexed.leaf _)) = nothing
  initLast (tree {h = suc _} t)    with Indexed.initLast t
  ... | (k , _ , _ , t′) = just (tree (Indexed.castʳ t′ [ _ ]<⊤⁺) , k)

  -- The input does not need to be ordered.

  fromList : List (K& V) → Tree V
  fromList = List.foldr (uncurry insert) empty

  -- Returns an ordered list.

  toList : Tree V → List (K& V)
  toList (tree t) = DiffList.toList (Indexed.toDiffList t)

  -- Naive implementations of union.

module _ {v w} {V : Value v} {W : Value w} where
  private
    Val = Value.family V
    Wal = Value.family W

  unionWith : (∀ {k} → Val k → Maybe (Wal k) → Wal k) →
              -- Left → right → result.
              Tree V → Tree W → Tree W
  unionWith f t₁ t₂ =
    List.foldr (uncurry $ λ k v → insertWith k (f v)) t₂ (toList t₁)

  -- Left-biased.

module _ {v} {V : Value v} where

  private Val = Value.family V

  union : Tree V → Tree V → Tree V
  union = unionWith F.const

  unionsWith : (∀ {k} → Val k → Maybe (Val k) → Val k) → List (Tree V) → Tree V
  unionsWith f ts = List.foldr (unionWith f) empty ts

  -- Left-biased.

  unions : List (Tree V) → Tree V
  unions = unionsWith F.const
