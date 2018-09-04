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
open import Size
open import Data.Product using (∃; uncurry)
open import Data.AVL.NonEmpty S as Tree⁺ using (Tree⁺)
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Maybe as Maybe using (Maybe; nothing; just) hiding (module Maybe)
open import Data.These as These using (These; this; that; these)
open import Function

-- A `Trie` is a tree branching over an alphabet of `Key`s. It stores values
-- indexed over the word (i.e. `List Key`) that was read to reach them.

-- Each `Node` in the `Trie` contains either a value, a non-empty `Tree` of
-- sub-`Trie`s reached by reading an extra letter, or both.

Word : Set k
Word = List Key

data Trie {v} (V : Word → Set v) (i : Size) : Set (v ⊔ k ⊔ r)
Tries : ∀ {v} (V : Word → Set v) → Size → Set (v ⊔ k ⊔ r)

data Trie V i where
  Node : {j : Size< i} → These (V []) (Tries V j) → Trie V i

Tries V j = Tree⁺ (λ k → Trie (V ∘′ (k ∷_)) j)

-- Query

lookup : ∀ {v} {V : Word → Set v} ks → Trie V ∞ → Maybe (V ks)
lookup []       (Node nd) = These.fromThis nd
lookup (k ∷ ks) (Node nd) = let open Maybe in do
  ts ← These.fromThat nd
  t  ← Tree⁺.lookup k ts
  lookup ks t

-- Construction

singleton : ∀ {v} {V : Word → Set v} ks → V ks → Trie V ∞
singleton []       v = Node (this v)
singleton (k ∷ ks) v = Node (that (Tree⁺.singleton k (singleton ks v)))

insertWith : ∀ {v} {V : Word → Set v} ks →
             (Maybe (V ks) → V ks) → Trie V ∞ → Trie V ∞
insertWith []       f (Node nd) =
  Node (These.fold (this ∘ f ∘ just) (these (f nothing)) (these ∘ f ∘ just) nd)
insertWith {v} {V} (k ∷ ks) f (Node nd) = Node $
  These.fold (λ v → these v (Tree⁺.singleton k end))
             (that ∘′ rec)
             (λ v → these v ∘′ rec)
  nd where

  end : Trie (V ∘′ (k ∷_)) ∞
  end = singleton ks (f nothing)

  rec : Tries V ∞ → Tries V ∞
  rec = Tree⁺.insertWith k end (const $ insertWith ks f)

module _ {v} {V : Word → Set v} where

  insert : ∀ ks → V ks → Trie V ∞ → Trie V ∞
  insert ks = insertWith ks ∘′ const

  fromList⁺ : List⁺ (∃ V) → Trie V ∞
  fromList⁺ = List⁺.foldr (uncurry insert) (uncurry singleton)

-- modify

map : ∀ {v w} {V : Word → Set v} {W : Word → Set w} {i} →
      (∀ {ks} → V ks → W ks) → Trie V i → Trie W i
map f (Node nd) = Node (These.map f (Tree⁺.map (map f)) nd)
