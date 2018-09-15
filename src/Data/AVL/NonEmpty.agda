------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty AVL trees
------------------------------------------------------------------------

-- AVL trees are balanced binary search trees.

-- The search tree invariant is specified using the technique
-- described by Conor McBride in his talk "Pivotal pragmatism".

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_ ; refl)

module Data.AVL.NonEmpty
  {k r} {Key : Set k} {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import Data.Bool.Base using (Bool)
open import Data.Empty
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; _++⁺_)
open import Data.Maybe.Base hiding (map)
open import Data.Nat.Base hiding (_<_; _⊔_; compare)
open import Data.Product hiding (map)
open import Data.Unit
open import Function
open import Level using (_⊔_; Lift; lift)

open IsStrictTotalOrder isStrictTotalOrder
import Data.AVL.Indexed Key isStrictTotalOrder as Indexed
open Indexed using (K&_ ; ⊥⁺ ; ⊤⁺; node; toList)

------------------------------------------------------------------------
-- Types and functions with hidden indices

-- NB: the height is non-zero thus guaranteeing that the AVL tree contains
-- at least one value.

data Tree⁺ {v} (V : Key → Set v) : Set (k ⊔ v ⊔ r) where
  tree : ∀ {h} → Indexed.Tree V ⊥⁺ ⊤⁺ (suc h) → Tree⁺ V

module _ {v} {V : Key → Set v} where

  singleton : (k : Key) → V k → Tree⁺ V
  singleton k v = tree (Indexed.singleton k v _)

  insert : (k : Key) → V k → Tree⁺ V → Tree⁺ V
  insert k v (tree t) with Indexed.insert k v t _
  ... | Indexed.0# , t′ = tree t′
  ... | Indexed.1# , t′ = tree t′
  ... | Indexed.## , t′

  insertWith : (k : Key) → V k → (V k → V k → V k) →
               Tree⁺ V → Tree⁺ V
  insertWith k v f (tree t) with Indexed.insertWith k v f t _
  ... | Indexed.0# , t′ = tree t′
  ... | Indexed.1# , t′ = tree t′
  ... | Indexed.## , t′

  delete : Key → Tree⁺ V → Maybe (Tree⁺ V)
  delete k (tree {h} t) with Indexed.delete k t
  ... | Indexed.1# , t′ = just (tree t′)
  delete k (tree {0}     t) | Indexed.0# , t′ = nothing
  delete k (tree {suc h} t) | Indexed.0# , t′ = just (tree t′)
  ... | Indexed.## , t′

  lookup : (k : Key) → Tree⁺ V → Maybe (V k)
  lookup k (tree t) = Indexed.lookup k t

module _ {v w} {V : Key → Set v} {W : Key → Set w} where

  map : ({k : Key} → V k → W k) → Tree⁺ V → Tree⁺ W
  map f (tree t) = tree $ Indexed.map f t

module _ {v} {V : Key → Set v} where

  -- The input does not need to be ordered.

  fromList : List⁺ (K& V) → Tree⁺ V
  fromList = List⁺.foldr (uncurry insert) (uncurry singleton)

  -- The output is ordered

  toList⁺ : Tree⁺ V → List⁺ (K& V)
  toList⁺ (tree (node k&v l r bal)) = toList l ++⁺ k&v ∷ toList r
