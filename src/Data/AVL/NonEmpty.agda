------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty AVL trees
------------------------------------------------------------------------

-- AVL trees are balanced binary search trees.

-- The search tree invariant is specified using the technique
-- described by Conor McBride in his talk "Pivotal pragmatism".

open import Relation.Binary using (StrictTotalOrder)

module Data.AVL.NonEmpty
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Bool.Base using (Bool)
open import Data.Empty
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; _++⁺_)
open import Data.Maybe.Base hiding (map)
open import Data.Nat.Base hiding (_<_; _⊔_; compare)
open import Data.Product hiding (map)
open import Data.Unit
open import Function
open import Level using (_⊔_; Lift; lift)
open import Relation.Unary

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
open import Data.AVL.Value Eq.setoid
import Data.AVL.Indexed strictTotalOrder as Indexed
open Indexed using (K&_ ; ⊥⁺ ; ⊤⁺; node; toList)

------------------------------------------------------------------------
-- Types and functions with hidden indices

-- NB: the height is non-zero thus guaranteeing that the AVL tree contains
-- at least one value.

data Tree⁺ {v} (V : Value v) : Set (a ⊔ v ⊔ ℓ₂) where
  tree : ∀ {h} → Indexed.Tree V ⊥⁺ ⊤⁺ (suc h) → Tree⁺ V

module _ {v} {V : Value v} where

  private
    Val = Value.family V

  singleton : (k : Key) → Val k → Tree⁺ V
  singleton k v = tree (Indexed.singleton k v _)

  insert : (k : Key) → Val k → Tree⁺ V → Tree⁺ V
  insert k v (tree t) with Indexed.insert k v t _
  ... | Indexed.0# , t′ = tree t′
  ... | Indexed.1# , t′ = tree t′
  ... | Indexed.## , t′

  insertWith : (k : Key) → (Maybe (Val k) → Val k) → Tree⁺ V → Tree⁺ V
  insertWith k f (tree t) with Indexed.insertWith k f t _
  ... | Indexed.0# , t′ = tree t′
  ... | Indexed.1# , t′ = tree t′
  ... | Indexed.## , t′

  delete : Key → Tree⁺ V → Maybe (Tree⁺ V)
  delete k (tree {h} t) with Indexed.delete k t _
  ... | Indexed.1# , t′ = just (tree t′)
  delete k (tree {0}     t) | Indexed.0# , t′ = nothing
  delete k (tree {suc h} t) | Indexed.0# , t′ = just (tree t′)
  ... | Indexed.## , t′

  lookup : (k : Key) → Tree⁺ V → Maybe (Val k)
  lookup k (tree t) = Indexed.lookup k t _

module _ {v w} {V : Value v} {W : Value w} where

  private
    Val = Value.family V
    Wal = Value.family W

  map : ∀[ Val ⇒ Wal ] → Tree⁺ V → Tree⁺ W
  map f (tree t) = tree $ Indexed.map f t

module _ {v} {V : Value v} where

  -- The input does not need to be ordered.

  fromList⁺ : List⁺ (K& V) → Tree⁺ V
  fromList⁺ = List⁺.foldr (uncurry insert) (uncurry singleton)

  -- The output is ordered

  toList⁺ : Tree⁺ V → List⁺ (K& V)
  toList⁺ (tree (node k&v l r bal)) = toList l ++⁺ k&v ∷ toList r
