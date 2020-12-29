------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees where at least one element satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Map.Relation.Unary.Any
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (ℕ)
open import Data.Product as Prod using (_×_;_,_; ∃; proj₂)
open import Function.Base
open import Level using (Level; _⊔_)

open import Relation.Nullary using (Dec; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
open import Data.Tree.AVL.Map strictTotalOrder as Map using (Map)
import Data.Tree.AVL.Relation.Unary.Any strictTotalOrder as Mapₚ

private
  variable
    v p q : Level
    V : Set v
    P : Pred V p
    Q : Pred V q
    m : Map V

------------------------------------------------------------------------
-- Definition

-- Given a predicate P, Any P t is a path to one element in t that satisfies P.
-- There may be others.
-- See `Relation.Unary` for an explanation of predicates.

Any : {V : Set v} → Pred (Key × V) p → Pred (Map V) (a ⊔ ℓ₂ ⊔ v ⊔ p)
Any P = Mapₚ.Any (Prod.curry P)

------------------------------------------------------------------------
-- Operations on Any

map : P ⊆ Q → Any P ⊆ Any Q
map f = Mapₚ.map f

lookup : Any P m → Key
lookup = Mapₚ.lookup

-- If any element satisfies P, then P is satisfied.

satisfied : Any P m → ∃ P
satisfied p = let (k , (v , pkv)) = Mapₚ.satisfied p in ((k , v) , pkv)

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

any? : Decidable P → Decidable (Any P)
any? P? = Mapₚ.any? (λ {k} v → P? (k , v))

satisfiable : Satisfiable P → Satisfiable (Any P)
satisfiable ((k , v) , p) = Mapₚ.satisfiable k (v , p)
