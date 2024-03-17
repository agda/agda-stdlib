------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees where at least one element satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Map.Relation.Unary.Any
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Product.Base as Product using (_×_; ∃; _,_)
open import Function.Base using (_∘_; _∘′_; id)
open import Level using (Level; _⊔_)

open import Relation.Unary

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
open import Data.Tree.AVL.Map strictTotalOrder using (Map)
open import Data.Tree.AVL.Indexed strictTotalOrder using (toPair)
import Data.Tree.AVL.Relation.Unary.Any strictTotalOrder as Map

private
  variable
    v p q : Level
    V : Set v
    P : Pred V p
    Q : Pred V q
    m : Map V

------------------------------------------------------------------------
-- Definition

-- Given a predicate P, Any P t describes a path in t to an element that
-- satisfies P. There may be others.
-- See `Relation.Unary` for an explanation of predicates.

Any : {V : Set v} → Pred (Key × V) p → Pred (Map V) (a ⊔ ℓ₂ ⊔ v ⊔ p)
Any P = Map.Any (P ∘′ toPair)

------------------------------------------------------------------------
-- Operations on Any

map : P ⊆ Q → Any P ⊆ Any Q
map f = Map.map f

lookup : Any {V = V} P m → Key × V
lookup = toPair ∘′ Map.lookup

lookupKey : Any P m → Key
lookupKey = Map.lookupKey

-- If any element satisfies P, then P is satisfied.

satisfied : Any P m → ∃ P
satisfied = Product.map toPair id ∘′ Map.satisfied

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

any? : Decidable P → Decidable (Any P)
any? P? = Map.any? (P? ∘ toPair)

satisfiable : Satisfiable P → Satisfiable (Any P)
satisfiable ((k , v) , p) = Map.satisfiable k (v , p)
