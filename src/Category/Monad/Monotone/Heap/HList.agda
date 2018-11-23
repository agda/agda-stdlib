-- An example implementation of the monotone HeapMonad
-- using heterogeneous lists as a memory model.

import Relation.Unary.Closure.Preorder as Closure
import Relation.Binary.PropositionalEquality as P
open import Data.List.Relation.Prefix.Heterogeneous.Properties using (preorder)
open import Data.List

module Category.Monad.Monotone.Heap.HList
  (T : Set)
  (V : T → List T → Set)
  ⦃ wkV : ∀ {a} → Closure.Closed (preorder P.isEquivalence) (V a) ⦄ where

open import Function
open import Data.Product
open import Data.List.All as All
open import Data.List.All.Properties
open import Data.List.Any
open import Data.List.Any.Properties
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Prefix.Heterogeneous
import Data.List.Relation.Pointwise as PW

open import Relation.Unary using (Pred)
open import Relation.Binary using (Preorder)

open import Category.Monad using (RawMonad)

ord : Preorder _ _ _
ord = (preorder {A = T} P.isEquivalence)

open Preorder ord renaming (refl to ∼-refl)
open import Relation.Unary.Closure.Preorder ord
open Closed ⦃...⦄

instance
  _ = ∼-closed

  ∈-closed : ∀ {x} → Closed (x ∈_)
  ∈-closed = record
    { next = λ x∈xs xs∼ys → prefix⁺ (flip P.trans) xs∼ys x∈xs }

  All-closed : ∀ {ys} → Closed (λ xs → All (λ y → V y xs) ys)
  All-closed = record
    { next = λ pys xs∼zs → All.map (λ p → next p xs∼zs) pys }

HeapT : Set
HeapT = List T

Heap : Pred HeapT _
Heap = λ W → All (λ a → V a W) W

open import Category.Monad.Monotone ord
open import Category.Monad.Monotone.State ord Heap
open import Category.Monad.Monotone.Heap ord T V Heap _∈_

module _ {M : Set → Set}(mon : RawMonad M) where
  private module M = RawMonad mon

  open HeapMonad
  hlist-heap-monad : HeapMonad (MST M)
  super  hlist-heap-monad             = mst-monad-ops mon
  store  hlist-heap-monad {x}{xs} v μ =
    let ext = fromView (PW.refl P.refl PrefixView.++ [ x ])
    in M.return (
      xs ∷ʳ x ,
      ext ,
      ∷ʳ⁺ (next μ ext) (next v ext) ,
      ++⁺ʳ xs (here P.refl))
  modify hlist-heap-monad ptr v μ     =
    M.return (-, ∼-refl , μ [ ptr ]≔ v , All.lookup μ ptr)
  deref  hlist-heap-monad ptr μ       =
    M.return (-, ∼-refl , μ , All.lookup μ ptr)

  open HeapMonadOps hlist-heap-monad public
