------------------------------------------------------------------------
-- The Agda standard library
--
-- Non empty trie, basic type and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

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

private
  module S = StrictTotalOrder S
open S using () renaming (Carrier to Key)

open import Data.List.Relation.Binary.Equality.Setoid S.Eq.setoid
open import Data.AVL.Value
open import Data.AVL.NonEmpty S as Tree⁺ using (Tree⁺)

-- A Trie⁺ is a tree branching over an alphabet of Keys. It stores values
-- indexed over the Word (i.e. List Key) that was read to reach them.
-- Each node in the Trie⁺ contains either a value, a non-empty Tree of
-- sub-Trie⁺ reached by reading an extra letter, or both.

Word : Set k
Word = List Key

eat : ∀ {v} → Value ≋-setoid v → Word → Value ≋-setoid v
Value.family   (eat V ks) = Value.family   V ∘′ (ks ++_)
Value.respects (eat V ks) = Value.respects V ∘′ ++⁺ ≋-refl

data Trie⁺ v (V : Value ≋-setoid (v ⊔ k ⊔ e ⊔ r)) : Size → Set (v ⊔ k ⊔ e ⊔ r)
Tries⁺ : ∀ v (V : Value ≋-setoid (v ⊔ k ⊔ e ⊔ r)) (i : Size) → Set (v ⊔ k ⊔ e ⊔ r)

map : ∀ v w V W {i} →
      let Val = Value.family V; Wal = Value.family W in
      ∀[ Val ⇒ Wal ] →
      Trie⁺ v V i → Trie⁺ w W i

data Trie⁺ v V where
  node : ∀ {i} → These (Value.family V []) (Tries⁺ v V i) → Trie⁺ v V (↑ i)

Tries⁺ v V j = Tree⁺ $ MkValue (λ k → Trie⁺ v (eat V (k ∷ [])) j)
                     $ λ eq → map v v _ _ (Value.respects V (eq ∷ ≋-refl))

map v w V W f (node t) = node $ These.map f (Tree⁺.map (map v w _ _ f)) t

-- Query

lookup : ∀ {v V} ks → Trie⁺ v V ∞ →
         Maybe (These (Value.family V ks) (Tries⁺ v (eat V ks) ∞))
lookup []       (node nd) = just (These.map₂ (Tree⁺.map id) nd)
lookup (k ∷ ks) (node nd) = let open Maybe in do
  ts ← These.fromThat nd
  t  ← Tree⁺.lookup k ts
  lookup ks t

module _ {v V} where

  lookupValue : ∀ ks → Trie⁺ v V ∞ → Maybe (Value.family V ks)
  lookupValue ks t = lookup ks t Maybe.>>= These.fromThis

  lookupTries⁺ : ∀ ks → Trie⁺ v V ∞ → Maybe (Tries⁺ v (eat V ks) ∞)
  lookupTries⁺ ks t = lookup ks t Maybe.>>= These.fromThat

  lookupTrie⁺ : ∀ k → Trie⁺ v V ∞ → Maybe (Trie⁺ v (eat V (k ∷ [])) ∞)
  lookupTrie⁺ k t = lookupTries⁺ [] t Maybe.>>= Tree⁺.lookup k

-- Construction

singleton : ∀ {v V} ks → Value.family V ks → Trie⁺ v V ∞
singleton []       v = node (this v)
singleton (k ∷ ks) v = node (that (Tree⁺.singleton k (singleton ks v)))

insertWith : ∀ {v V} ks → let Val = Value.family V in
             (Maybe (Val ks) → Val ks) → Trie⁺ v V ∞ → Trie⁺ v V ∞
insertWith []       f (node nd) =
  node (These.fold (this ∘ f ∘ just) (these (f nothing)) (these ∘ f ∘ just) nd)
insertWith {v} {V} (k ∷ ks) f (node {j} nd) = node $
  These.fold (λ v → these v (Tree⁺.singleton k end))
             (that ∘′ rec)
             (λ v → these v ∘′ rec)
  nd where

  end : Trie⁺ v (eat V (k ∷ [])) ∞
  end = singleton ks (f nothing)

  rec : Tries⁺ v V ∞ → Tries⁺ v V ∞
  rec = Tree⁺.insertWith k (maybe′ (insertWith ks f) end)

module _ {v} {V : Value ≋-setoid (v ⊔ k ⊔ e ⊔ r)} where

  private Val = Value.family V

  insert : ∀ ks → Val ks → Trie⁺ v V ∞ → Trie⁺ v V ∞
  insert ks = insertWith ks ∘′ F.const

  fromList⁺ : List⁺ (∃ Val) → Trie⁺ v V ∞
  fromList⁺ = List⁺.foldr (uncurry insert) (uncurry singleton)

toList⁺ : ∀ {v V i} → let Val = Value.family V in Trie⁺ v V i → List⁺ (∃ Val)
toList⁺ (node nd) = These.mergeThese List⁺._⁺++⁺_
                    $ These.map fromVal fromTries⁺ nd
  where

  fromVal    = [_] ∘′ -,_
  fromTries⁺ = concatMap (uncurry λ k → List⁺.map (Prod.map (k ∷_) id) ∘′ toList⁺)
             ∘′ Tree⁺.toList⁺

-- Modification

-- Deletion

deleteWith : ∀ {v V i} ks →
             (∀ {i} → Trie⁺ v (eat V ks) i → Maybe (Trie⁺ v (eat V ks) i)) →
             Trie⁺ v V i → Maybe (Trie⁺ v V i)
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

module _ {v V} where

  deleteTrie⁺ : ∀ {i} (ks : Word) → Trie⁺ v V i → Maybe (Trie⁺ v V i)
  deleteTrie⁺ ks = deleteWith ks (F.const nothing)

  deleteValue : ∀ {i} (ks : Word) → Trie⁺ v V i → Maybe (Trie⁺ v V i)
  deleteValue ks = deleteWith ks $ λ where
    (node nd) → Maybe.map node $′ These.deleteThis nd

  deleteTries⁺ : ∀ {i} (ks : Word) → Trie⁺ v V i → Maybe (Trie⁺ v V i)
  deleteTries⁺ ks = deleteWith ks $ λ where
    (node nd) → Maybe.map node $′ These.deleteThat nd
