------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty AVL trees
------------------------------------------------------------------------

-- AVL trees are balanced binary search trees.

-- The search tree invariant is specified using the technique
-- described by Conor McBride in his talk "Pivotal pragmatism".

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.NonEmpty
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Bool.Base using (Bool)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; _++⁺_)
open import Data.Maybe.Base hiding (map)
open import Data.Nat.Base hiding (_<_; _⊔_; compare)
open import Data.Product.Base hiding (map)
open import Function.Base using (_$_; _∘′_)
open import Level using (_⊔_)
open import Relation.Unary using (IUniversal; _⇒_)

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
open import Data.Tree.AVL.Value Eq.setoid
import Data.Tree.AVL.Indexed strictTotalOrder as Indexed
open Indexed using (⊥⁺; ⊤⁺; ⊥⁺<⊤⁺; ⊥⁺<[_]<⊤⁺; ⊥⁺<[_]; [_]<⊤⁺; node; toList)

------------------------------------------------------------------------
-- Types and functions with hidden indices

-- NB: the height is non-zero thus guaranteeing that the AVL tree
-- contains at least one value.

data Tree⁺ {v} (V : Value v) : Set (a ⊔ v ⊔ ℓ₂) where
  tree : ∀ {h} → Indexed.Tree V ⊥⁺ ⊤⁺ (suc h) → Tree⁺ V

module _ {v} {V : Value v} where

  private
    Val = Value.family V

  singleton : (k : Key) → Val k → Tree⁺ V
  singleton k v = tree (Indexed.singleton k v ⊥⁺<[ k ]<⊤⁺)

  insert : (k : Key) → Val k → Tree⁺ V → Tree⁺ V
  insert k v (tree t) with Indexed.insert k v t ⊥⁺<[ k ]<⊤⁺
  ... | Indexed.0# , t′ = tree t′
  ... | Indexed.1# , t′ = tree t′

  insertWith : (k : Key) → (Maybe (Val k) → Val k) → Tree⁺ V → Tree⁺ V
  insertWith k f (tree t) with Indexed.insertWith k f t ⊥⁺<[ k ]<⊤⁺
  ... | Indexed.0# , t′ = tree t′
  ... | Indexed.1# , t′ = tree t′

  delete : Key → Tree⁺ V → Maybe (Tree⁺ V)
  delete k (tree {h}     t) with Indexed.delete k t ⊥⁺<[ k ]<⊤⁺
  delete k (tree {h}     t) | Indexed.1# , t′ = just (tree t′)
  delete k (tree {0}     t) | Indexed.0# , t′ = nothing
  delete k (tree {suc h} t) | Indexed.0# , t′ = just (tree t′)

  lookup : Tree⁺ V → (k : Key) → Maybe (Val k)
  lookup (tree t) k = Indexed.lookup t k ⊥⁺<[ k ]<⊤⁺

module _ {v w} {V : Value v} {W : Value w} where

  private
    Val = Value.family V
    Wal = Value.family W

  map : ∀[ Val ⇒ Wal ] → Tree⁺ V → Tree⁺ W
  map f (tree t) = tree $ Indexed.map f t

module _ {v} {V : Value v} where

  -- The input does not need to be ordered.

  fromList⁺ : List⁺ (K& V) → Tree⁺ V
  fromList⁺ = List⁺.foldr (uncurry insert ∘′ toPair) (uncurry singleton ∘′ toPair)

  -- The output is ordered

  toList⁺ : Tree⁺ V → List⁺ (K& V)
  toList⁺ (tree (node k&v l r bal)) = toList l ++⁺ k&v ∷ toList r
