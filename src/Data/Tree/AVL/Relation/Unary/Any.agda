------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees where at least one element satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Relation.Unary.Any
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Product as Prod using (∃)
open import Function.Base using (_∘_; _$_)
open import Level using (Level; _⊔_)

open import Relation.Nullary.Decidable using (map′)
open import Relation.Unary

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
open import Data.Tree.AVL.Indexed strictTotalOrder as Indexed using (K&_; _,_)
open import Data.Tree.AVL strictTotalOrder using (Tree; tree; Value)
import Data.Tree.AVL.Indexed.Relation.Unary.Any strictTotalOrder as AVLₚ


private
  variable
    v p q : Level
    V : Value v
    t : Tree V
    P : Pred (K& V) p
    Q : Pred (K& V) q

------------------------------------------------------------------------
-- Definition

-- Given a predicate P, Any P t describes a path in t to an element that
-- satisfies P. There may be others.
-- See `Relation.Unary` for an explanation of predicates.

data Any {V : Value v} (P : Pred (K& V) p) :
         Tree V → Set (p ⊔ a ⊔ v ⊔ ℓ₂) where
  tree : ∀ {h t} → AVLₚ.Any P t → Any P (tree {h = h} t)

------------------------------------------------------------------------
-- Operations on Any

map : P ⊆ Q → Any P t → Any Q t
map f (tree p) = tree (AVLₚ.map f p)

lookup : Any {V = V} P t → K& V
lookup (tree p) = AVLₚ.lookup p

lookupKey : Any P t → Key
lookupKey (tree p) = AVLₚ.lookupKey p

-- If any element satisfies P, then P is satisfied.

satisfied : Any P t → ∃ P
satisfied (tree p) = AVLₚ.satisfied p

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

any? : Decidable P → Decidable (Any {V = V} P)
any? P? (tree p) = map′ tree (λ where (tree p) → p) (AVLₚ.any? P? p)

satisfiable : (k : Key) → Satisfiable (P ∘ (k ,_)) → Satisfiable (Any {V = V} P)
satisfiable k sat = Prod.map tree tree
                  $ AVLₚ.satisfiable Indexed.⊥⁺<[ k ] Indexed.[ k ]<⊤⁺ sat
