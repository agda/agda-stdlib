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

open import Data.Nat.Base using (ℕ)
open import Data.Product as Prod using (_,_; ∃₂; -,_; proj₁; proj₂)
open import Function.Base
open import Level using (Level; _⊔_)

open import Relation.Nullary using (Dec; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
import Data.Tree.AVL.Indexed strictTotalOrder as Indexed
open import Data.Tree.AVL strictTotalOrder as AVL using (Tree; tree; Value)
import Data.Tree.AVL.Indexed.Relation.Unary.Any strictTotalOrder as AVLₚ


private
  variable
    v p q : Level
    V : Value v
    n : ℕ

------------------------------------------------------------------------
-- Definition

-- Given a predicate P, Any P t is a path to one element in t that satisfies P.
-- There may be others.
-- See `Relation.Unary` for an explanation of predicates.

data Any {V : Value v} (P : ∀ k → Value.family V k → Set p) :
         Tree V → Set (p ⊔ a ⊔ v ⊔ ℓ₂) where
  tree : ∀ {h t} → AVLₚ.Any P t → Any P (tree {h = h} t)

------------------------------------------------------------------------
-- Operations on Any

module _ {V : Value v}
  {P : ∀ k → Value.family V k → Set p}
  {Q : ∀ k → Value.family V k → Set q}
  where

  map : ∀ {t : Tree V} → (∀ {k} → P k ⊆ Q k) → Any P t → Any Q t
  map f (tree p) = tree (AVLₚ.map f p)

module _ {V : Value v}
  {P : ∀ k → Value.family V k → Set p}
  where

  lookup : ∀ {t : Tree V} → Any P t → Key
  lookup (tree p) = AVLₚ.lookup p

-- If any element satisfies P, then P is satisfied.

  satisfied : ∀ {t : Tree V} → Any P t → ∃₂ P
  satisfied (tree p) = AVLₚ.satisfied p

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

  any? : (∀ {k} → Decidable (P k)) → Decidable (Any {V = V} P)
  any? P? (tree p) = map′ tree (λ where (tree p) → p) (AVLₚ.any? P? p)

  satisfiable : (k : Key) → Satisfiable (P k) → Satisfiable (Any {V = V} P)
  satisfiable k sat = Prod.map tree tree
                    $ AVLₚ.satisfiable Indexed.⊥⁺<[ k ] Indexed.[ k ]<⊤⁺ sat
