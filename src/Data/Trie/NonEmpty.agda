------------------------------------------------------------------------
-- The Agda standard library
--
-- Non empty trie, basic type and operations
------------------------------------------------------------------------

open import Relation.Binary using (Rel; IsStrictTotalOrder)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

module Data.Trie.NonEmpty
  {k r} {Key : Set k} {_<_ : Rel Key r}
  (S : IsStrictTotalOrder _≡_ _<_) where

open import Level
open import Size
open import Category.Monad
open import Data.Product as Prod using (∃; uncurry; -,_)
open import Data.AVL.NonEmpty S as Tree⁺ using (Tree⁺)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.List.NonEmpty as List⁺ using (List⁺; [_]; concatMap)
open import Data.Maybe as Maybe using (Maybe; nothing; just) hiding (module Maybe)
open import Data.These as These using (These; this; that; these)
open import Function
import Function.Identity.Categorical as Identity
open import Relation.Unary using (_⇒_; IUniversal)

-- A Trie⁺ is a tree branching over an alphabet of Keys. It stores values
-- indexed over the Word (i.e. List Key) that was read to reach them.
-- Each node in the Trie⁺ contains either a value, a non-empty Tree of
-- sub-Trie⁺ reached by reading an extra letter, or both.

Word : Set k
Word = List Key

data Trie⁺ {v} (V : Word → Set v) (i : Size) : Set (v ⊔ k ⊔ r)
Tries⁺ : ∀ {v} (V : Word → Set v) → Size → Set (v ⊔ k ⊔ r)

data Trie⁺ V i where
  node : {j : Size< i} → These (V []) (Tries⁺ V j) → Trie⁺ V i

Tries⁺ V j = Tree⁺ (λ k → Trie⁺ (V ∘′ (k ∷_)) j)

-- Query

lookup : ∀ {v} {V : Word → Set v} ks → Trie⁺ V ∞ →
         Maybe (These (V ks) (Tries⁺ (V ∘′ (ks ++_)) ∞))
lookup []       (node nd) = just nd
lookup (k ∷ ks) (node nd) = let open Maybe in do
  ts ← These.fromThat nd
  t  ← Tree⁺.lookup k ts
  lookup ks t

lookupValue : ∀ {v} {V : Word → Set v} ks → Trie⁺ V ∞ → Maybe (V ks)
lookupValue ks t = lookup ks t Maybe.>>= These.fromThis

lookupTries⁺ : ∀ {v} {V : Word → Set v} ks → Trie⁺ V ∞ → Maybe (Tries⁺ (V ∘′ (ks ++_)) ∞)
lookupTries⁺ ks t = lookup ks t Maybe.>>= These.fromThat

-- Construction

singleton : ∀ {v} {V : Word → Set v} ks → V ks → Trie⁺ V ∞
singleton []       v = node (this v)
singleton (k ∷ ks) v = node (that (Tree⁺.singleton k (singleton ks v)))

insertWith : ∀ {v} {V : Word → Set v} ks →
             (Maybe (V ks) → V ks) → Trie⁺ V ∞ → Trie⁺ V ∞
insertWith []       f (node nd) =
  node (These.fold (this ∘ f ∘ just) (these (f nothing)) (these ∘ f ∘ just) nd)
insertWith {v} {V} (k ∷ ks) f (node nd) = node $
  These.fold (λ v → these v (Tree⁺.singleton k end))
             (that ∘′ rec)
             (λ v → these v ∘′ rec)
  nd where

  end : Trie⁺ (V ∘′ (k ∷_)) ∞
  end = singleton ks (f nothing)

  rec : Tries⁺ V ∞ → Tries⁺ V ∞
  rec = Tree⁺.insertWith k end (const $ insertWith ks f)

module _ {v} {V : Word → Set v} where

  insert : ∀ ks → V ks → Trie⁺ V ∞ → Trie⁺ V ∞
  insert ks = insertWith ks ∘′ const

  fromList⁺ : List⁺ (∃ V) → Trie⁺ V ∞
  fromList⁺ = List⁺.foldr (uncurry insert) (uncurry singleton)

toList⁺ : ∀ {v} {V : Word → Set v} {i} → Trie⁺ V i → List⁺ (∃ V)
toList⁺ (node nd) = These.mergeThese List⁺._⁺++⁺_
                  $ These.map fromVal fromTries⁺ nd
  where

  fromVal    = [_] ∘′ -,_
  fromTries⁺ = concatMap (uncurry λ k → List⁺.map (Prod.map (k ∷_) id) ∘′ toList⁺)
             ∘′ Tree⁺.toList⁺

-- Modification

map : ∀ {v w} {V : Word → Set v} {W : Word → Set w} {i} →
      ∀[ V ⇒ W ] → Trie⁺ V i → Trie⁺ W i
map f (node nd) = node (These.map f (Tree⁺.map (map f)) nd)


-- Deletion

deleteWith : ∀ {v} {V : Word → Set v} {i} ks →
             (∀ {i} → Trie⁺ (V ∘′ (ks ++_)) i → Maybe (Trie⁺ (V ∘′ (ks ++_)) i)) →
             Trie⁺ V i → Maybe (Trie⁺ V i)
deleteWith []       f t           = f t
deleteWith (k ∷ ks) f t@(node nd) = let open RawMonad Identity.monad in do
  just ts ← These.fromThat nd where _ → just t
  -- This would be a lot cleaner if we had
  -- Tree⁺.updateWith : ∀ k → (Maybe (V k) → Maybe (V k)) → AVL → AVL
  -- Instead we lookup the subtree, update it and either put it back in
  -- or delete the corresponding leaf depending on whether the result is successful.
  just t′ ← Tree⁺.lookup k ts where _ → just t
  Maybe.map node ∘′ Maybe.align (These.fromThis nd) $′ case deleteWith ks f t′ of λ where
    nothing  → Tree⁺.delete k ts
    (just u) → just (Tree⁺.insert k u ts)

module _ {v} {V : Word → Set v} where

  deleteTrie⁺ : ∀ {i} (ks : Word) → Trie⁺ V i → Maybe (Trie⁺ V i)
  deleteTrie⁺ ks = deleteWith ks (const nothing)

  deleteValue : ∀ {i} (ks : Word) → Trie⁺ V i → Maybe (Trie⁺ V i)
  deleteValue ks = deleteWith ks $ λ where
    (node nd) → Maybe.map node $′ These.deleteThis nd

  deleteTries⁺ : ∀ {i} (ks : Word) → Trie⁺ V i → Maybe (Trie⁺ V i)
  deleteTries⁺ ks = deleteWith ks $ λ where
    (node nd) → Maybe.map node $′ These.deleteThat nd
