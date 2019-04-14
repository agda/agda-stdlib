------------------------------------------------------------------------
-- The Agda standard library
--
-- Non empty trie, basic type and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Trie.NonEmpty {k e r} (S : StrictTotalOrder k e r) where

open import Level
open import Size
open import Category.Monad
open import Data.Product as Prod using (∃; uncurry; -,_)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.List.NonEmpty as List⁺ using (List⁺; [_]; concatMap)
open import Data.Maybe as Maybe using (Maybe; nothing; just; maybe′) hiding (module Maybe)
open import Data.These as These using (These; this; that; these)
open import Function as F
import Function.Identity.Categorical as Identity
open import Relation.Unary using (_⇒_; IUniversal)

open StrictTotalOrder S
  using (module Eq)
  renaming (Carrier to Key)

open import Data.List.Relation.Binary.Equality.Setoid Eq.setoid
open import Data.AVL.Value hiding (Value)
open import Data.AVL.Value ≋-setoid using (Value)
open import Data.AVL.NonEmpty S as Tree⁺ using (Tree⁺)
open Value

------------------------------------------------------------------------
-- Definition

-- A Trie⁺ is a tree branching over an alphabet of Keys. It stores values
-- indexed over the Word (i.e. List Key) that was read to reach them.
-- Each node in the Trie⁺ contains either a value, a non-empty Tree of
-- sub-Trie⁺ reached by reading an extra letter, or both.

Word : Set k
Word = List Key

eat : ∀ {v} → Value v → Word → Value v
family   (eat V ks) = family   V ∘′ (ks ++_)
respects (eat V ks) = respects V ∘′ ++⁺ ≋-refl

data Trie⁺ {v} (V : Value v) : Size → Set (v ⊔ k ⊔ e ⊔ r)
Tries⁺ : ∀ {v} (V : Value v) (i : Size) → Set (v ⊔ k ⊔ e ⊔ r)

map : ∀ {v w} (V : Value v) (W : Value w) {i} →
      ∀[ family V ⇒ family W ] →
      Trie⁺ V i → Trie⁺ W i

data Trie⁺ V where
  node : ∀ {i} → These (family V []) (Tries⁺ V i) → Trie⁺ V (↑ i)

Tries⁺ V j = Tree⁺ $ MkValue (λ k → Trie⁺ (eat V (k ∷ [])) j)
                   $ λ eq → map _ _ (respects V (eq ∷ ≋-refl))

map V W f (node t) = node $ These.map f (Tree⁺.map (map _ _ f)) t

------------------------------------------------------------------------
-- Query

lookup : ∀ {v} {V : Value v} ks → Trie⁺ V ∞ →
         Maybe (These (family V ks) (Tries⁺ (eat V ks) ∞))
lookup []       (node nd) = just (These.map₂ (Tree⁺.map id) nd)
lookup (k ∷ ks) (node nd) = let open Maybe in do
  ts ← These.fromThat nd
  t  ← Tree⁺.lookup k ts
  lookup ks t

module _ {v} {V : Value v} where

  lookupValue : ∀ (ks : Word) → Trie⁺ V ∞ → Maybe (family V ks)
  lookupValue ks t = lookup ks t Maybe.>>= These.fromThis

  lookupTries⁺ : ∀ ks → Trie⁺ V ∞ → Maybe (Tries⁺ (eat V ks) ∞)
  lookupTries⁺ ks t = lookup ks t Maybe.>>= These.fromThat

  lookupTrie⁺ : ∀ k → Trie⁺ V ∞ → Maybe (Trie⁺ (eat V (k ∷ [])) ∞)
  lookupTrie⁺ k t = lookupTries⁺ [] t Maybe.>>= Tree⁺.lookup k

------------------------------------------------------------------------
-- Construction

singleton : ∀ {v} {V : Value v} ks → family V ks → Trie⁺ V ∞
singleton []       v = node (this v)
singleton (k ∷ ks) v = node (that (Tree⁺.singleton k (singleton ks v)))

insertWith : ∀ {v} {V : Value v} ks → (Maybe (family V ks) → family V ks) →
             Trie⁺ V ∞ → Trie⁺ V ∞
insertWith []       f (node nd) =
  node (These.fold (this ∘ f ∘ just) (these (f nothing)) (these ∘ f ∘ just) nd)
insertWith {v} {V} (k ∷ ks) f (node {j} nd) = node $
  These.fold (λ v → these v (Tree⁺.singleton k end))
             (that ∘′ rec)
             (λ v → these v ∘′ rec)
             nd
  where

  end : Trie⁺ (eat V (k ∷ [])) ∞
  end = singleton ks (f nothing)

  rec : Tries⁺ V ∞ → Tries⁺ V ∞
  rec = Tree⁺.insertWith k (maybe′ (insertWith ks f) end)

module _ {v} {V : Value v} where

  private Val = family V

  insert : ∀ ks → Val ks → Trie⁺ V ∞ → Trie⁺ V ∞
  insert ks = insertWith ks ∘′ F.const

  fromList⁺ : List⁺ (∃ Val) → Trie⁺ V ∞
  fromList⁺ = List⁺.foldr (uncurry insert) (uncurry singleton)

toList⁺ : ∀ {v} {V : Value v} {i} → let Val = Value.family V in
          Trie⁺ V i → List⁺ (∃ Val)
toList⁺ (node nd) = These.mergeThese List⁺._⁺++⁺_
                    $ These.map fromVal fromTries⁺ nd
  where

  fromVal    = [_] ∘′ -,_
  fromTries⁺ = concatMap (uncurry λ k → List⁺.map (Prod.map (k ∷_) id) ∘′ toList⁺)
             ∘′ Tree⁺.toList⁺

------------------------------------------------------------------------
-- Modification

-- Deletion

deleteWith : ∀ {v} {V : Value v} {i} ks →
             (∀ {i} → Trie⁺ (eat V ks) i → Maybe (Trie⁺ (eat V ks) i)) →
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

module _ {v} {V : Value v} where

  deleteTrie⁺ : ∀ {i} (ks : Word) → Trie⁺ V i → Maybe (Trie⁺ V i)
  deleteTrie⁺ ks = deleteWith ks (F.const nothing)

  deleteValue : ∀ {i} (ks : Word) → Trie⁺ V i → Maybe (Trie⁺ V i)
  deleteValue ks = deleteWith ks $ λ where
    (node nd) → Maybe.map node $′ These.deleteThis nd

  deleteTries⁺ : ∀ {i} (ks : Word) → Trie⁺ V i → Maybe (Trie⁺ V i)
  deleteTries⁺ ks = deleteWith ks $ λ where
    (node nd) → Maybe.map node $′ These.deleteThat nd
