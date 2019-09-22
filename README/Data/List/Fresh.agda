------------------------------------------------------------------------
-- The Agda standard library
--
-- Example use case for a fresh list: sorted list
------------------------------------------------------------------------

module README.Data.List.Fresh where

open import Data.Nat
open import Data.List.Base
open import Data.List.Fresh
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs)
open import Data.Product
open import Relation.Nary using (⌊_⌋; fromWitness)

-- A sorted list of natural numbers can be seen as a fresh list
-- where the notion of freshness is being smaller than all the
-- existing entries

SortedList : Set
SortedList = List# ℕ _<_

_ : SortedList
_ = cons 0 (cons 1 (cons 3 (cons 10 [] _)
      (s≤s (s≤s (s≤s (s≤s z≤n))) , _))
      (s≤s (s≤s z≤n) , s≤s (s≤s z≤n) , _))
      (s≤s z≤n , s≤s z≤n , s≤s z≤n , _)

-- Clearly, writing these by hand can pretty quickly become quite cumbersome
-- Luckily, if the notion of freshness we are using is decidable, we can
-- make most of the proofs inferrable by using the erasure of the relation
-- rather than the relation itself!

-- We call this new type *I*SortedList because all the proofs will be implicit.

ISortedList : Set
ISortedList = List# ℕ ⌊ _<?_ ⌋

-- The same example is now much shorter. It looks pretty much like a normal list
-- except that we know for sure that it is well ordered.

ins : ISortedList
ins = 0 ∷# 1 ∷# 3 ∷# 10 ∷# []

-- Indeed we can extract the support list together with a proof that it
-- is ordered thanks to the combined action of toList converting a fresh
-- list to a pair of a list and a proof and fromWitness which "unerases"
-- a proof.

ns : List ℕ
ns = proj₁ (toList ins)

sorted : AllPairs _<_ ns
sorted = AllPairs.map (fromWitness _<_ _<?_) (proj₂ (toList ins))

-- See the following module for an applied use-case of fresh lists
open import README.Data.Trie.NonDependent
