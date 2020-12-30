------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees
------------------------------------------------------------------------

-- AVL trees are balanced binary search trees.

-- The search tree invariant is specified using the technique
-- described by Conor McBride in his talk "Pivotal pragmatism".

-- See README.Data.Tree.AVL for examples of how to use AVL trees.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (Bool)
import Data.DifferenceList as DiffList
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just; is-just)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product hiding (map)
open import Function.Base as F
open import Level using (Level; _⊔_)
open import Relation.Unary using (IUniversal; _⇒_)

private
  variable
    l : Level
    A : Set l

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
import Data.Tree.AVL.Indexed strictTotalOrder as Indexed
open Indexed using (⊥⁺; ⊤⁺; ⊥⁺<⊤⁺; ⊥⁺<[_]<⊤⁺; ⊥⁺<[_]; [_]<⊤⁺)

------------------------------------------------------------------------
-- Re-export some core definitions publically

open Indexed using (K&_;_,_; toPair; fromPair; Value; MkValue; const) public

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

  headTail : Tree V → Maybe (K& V × Tree V)
  headTail (tree (Indexed.leaf _)) = nothing
  headTail (tree {h = suc _} t)    with Indexed.headTail t
  ... | (k , _ , _ , t′) = just (k , tree (Indexed.castˡ ⊥⁺<[ _ ] t′))

  initLast : Tree V → Maybe (Tree V × K& V)
  initLast (tree (Indexed.leaf _)) = nothing
  initLast (tree {h = suc _} t)    with Indexed.initLast t
  ... | (k , _ , _ , t′) = just (tree (Indexed.castʳ t′ [ _ ]<⊤⁺) , k)

  foldr : (∀ {k} → Val k → A → A) → A → Tree V → A
  foldr cons nil (tree t) = Indexed.foldr cons nil t

  -- The input does not need to be ordered.

  fromList : List (K& V) → Tree V
  fromList = List.foldr (uncurry insert ∘′ toPair) empty

  -- Returns an ordered list.

  toList : Tree V → List (K& V)
  toList (tree t) = DiffList.toList (Indexed.toDiffList t)

  size : Tree V → ℕ
  size (tree t) = Indexed.size t

------------------------------------------------------------------------
-- Naive implementation of union

module _ {v w} {V : Value v} {W : Value w} where
  private
    Val = Value.family V
    Wal = Value.family W

  unionWith : (∀ {k} → Val k → Maybe (Wal k) → Wal k) →
              -- left → right → result.
              Tree V → Tree W → Tree W
  unionWith f t₁ t₂ = foldr (λ {k} v → insertWith k (f v)) t₂ t₁

module _ {v} {V : Value v} where

  private Val = Value.family V

  -- Left-biased.
  union : Tree V → Tree V → Tree V
  union = unionWith F.const

  unionsWith : (∀ {k} → Val k → Maybe (Val k) → Val k) → List (Tree V) → Tree V
  unionsWith f ts = List.foldr (unionWith f) empty ts

  -- Left-biased.
  unions : List (Tree V) → Tree V
  unions = unionsWith F.const

------------------------------------------------------------------------
-- Naive implementation of intersection

module _ {v w x} {V : Value v} {W : Value w} {X : Value x} where
  private
    Val = Value.family V
    Wal = Value.family W
    Xal = Value.family X

  intersectionWith : (∀ {k} → Val k → Wal k → Xal k) →
                     Tree V → Tree W → Tree X
  intersectionWith f t₁ t₂ = foldr cons empty t₁ where

    cons :  ∀ {k} → Val k → Tree X → Tree X
    cons {k} v = case lookup k t₂ of λ where
      nothing  → id
      (just w) → insert k (f v w)

module _ {v} {V : Value v} where
  private
    Val = Value.family V

  -- Left-biased.
  intersection : Tree V → Tree V → Tree V
  intersection = intersectionWith F.const

  intersectionsWith : (∀ {k} → Val k → Val k → Val k) →
                      List (Tree V) → Tree V
  intersectionsWith f []       = empty
  intersectionsWith f (t ∷ ts) = List.foldl (intersectionWith f) t ts
  -- We are using foldl so that we are indeed forming t₁ ∩ ⋯ ∩ tₙ for
  -- the input list [t₁,⋯,tₙ]. If we were to use foldr, we would form
  -- t₂ ∩ ⋯ ∩ tₙ ∩ t₁ instead!

  -- Left-biased.
  intersections : List (Tree V) → Tree V
  intersections = intersectionsWith F.const
