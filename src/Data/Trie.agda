------------------------------------------------------------------------
-- The Agda standard library
--
-- Trie, basic type and operations
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

module Data.Trie
  {k r} {Key : Set k} {_<_ : Rel Key r}
  (S : IsStrictTotalOrder _≡_ _<_) where

open import Level
open import Data.Product
open import Data.AVL.NonEmpty S as Tree⁺ using (Tree⁺)
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Maybe as Maybe using (Maybe; nothing; just) hiding (module Maybe)
open import Data.These as These
open import Function

-- A `Trie` is a tree branching over an alphabet of `Key`s. It stores values
-- indexed over the word (i.e. `List Key`) that was read to reach them.

-- Each `Node` in the `Trie` contains either a value, a non-empty `Tree` of
-- sub-`Trie`s reached by reading an extra letter, or both.

Word : Set k
Word = List Key

data Trie {v} (V : Word → Set v) : Set (v ⊔ k ⊔ r) where
  Node : These (V []) (Tree⁺ (λ k → Trie (V ∘ (k ∷_)))) → Trie V

-- Query

lookup : ∀ {v} {V : Word → Set v} ks → Trie V → Maybe (V ks)
lookup []       (Node nd) = fromThis nd
lookup (k ∷ ks) (Node nd) = let open Maybe in do
  ts ← fromThat nd
  t  ← Tree⁺.lookup k ts
  lookup ks t

-- Construction

singleton : ∀ {v} {V : Word → Set v} ks → V ks → Trie V
singleton []       v = Node (this v)
singleton (k ∷ ks) v = Node (that (Tree⁺.singleton k (singleton ks v)))

insertWith : ∀ {v} {V : Word → Set v} ks →
             (Maybe (V ks) → V ks) → Trie V → Trie V
insertWith []       f (Node nd) =
  Node (These.fold (this ∘ f ∘ just) (these (f nothing)) (these ∘ f ∘ just) nd)
insertWith (k ∷ ks) f (Node nd) =
  let end = singleton ks (f nothing)
      rec = Tree⁺.insertWith k end (const $ insertWith ks f)
  in Node $ These.fold (λ v → these v (Tree⁺.singleton k end))
                       (that ∘′ rec)
                       (λ v → these v ∘′ rec)
            nd

module _ {v} {V : Word → Set v} where

  insert : ∀ ks → V ks → Trie V → Trie V
  insert ks = insertWith ks ∘′ const

  fromList⁺ : List⁺ (∃ V) → Trie V
  fromList⁺ = List⁺.foldr (uncurry insert) (uncurry singleton)
