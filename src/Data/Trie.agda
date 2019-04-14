------------------------------------------------------------------------
-- The Agda standard library
--
-- Trie, basic type and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Relation.Binary using (Rel; StrictTotalOrder)

module Data.Trie {k e r} (S : StrictTotalOrder k e r) where

open import Level
open import Size
open import Data.List.Base using (List; []; _∷_; _++_)
import Data.List.NonEmpty as List⁺
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Product as Prod using (∃)
open import Data.These as These using (These)
open import Function
open import Relation.Unary using (IUniversal; _⇒_)

private
  module S = StrictTotalOrder S

open import Data.List.Relation.Binary.Equality.Setoid S.Eq.setoid
open import Data.AVL.Value using (Value; module Value)

------------------------------------------------------------------------
-- Definition

-- Trie is defined in terms of Trie⁺, the type of non-empty trie. This
-- guarantees that the trie is minimal: each path in the tree leads to
-- either a value or a number of non-empty sub-tries.

open import Data.Trie.NonEmpty S as Trie⁺ public
  using (Trie⁺; Tries⁺; Word; eat)

Trie : ∀ v V → Size → Set (v ⊔ k ⊔ e ⊔ r)
Trie v V i = Maybe (Trie⁺ v V i)

------------------------------------------------------------------------
-- Operations

-- Functions acting on Trie are wrappers for functions acting on Tries.
-- Sometimes the empty case is handled in a special way (e.g. insertWith
-- calls singleton when faced with an empty Trie).

module _ {v} {V : Value ≋-setoid (v ⊔ k ⊔ e ⊔ r)} where

  private Val = Value.family V

------------------------------------------------------------------------
-- Lookup

  lookup : ∀ ks → Trie v V ∞ → Maybe (These (Val ks) (Tries⁺ v (eat V ks) ∞))
  lookup ks t = t Maybe.>>= Trie⁺.lookup ks

  lookupValue : ∀ ks → Trie v V ∞ → Maybe (Val ks)
  lookupValue ks t = t Maybe.>>= Trie⁺.lookupValue ks

  lookupTries⁺ : ∀ ks → Trie v V ∞ → Maybe (Tries⁺ v (eat V ks) ∞)
  lookupTries⁺ ks t = t Maybe.>>= Trie⁺.lookupTries⁺ ks

  lookupTrie : ∀ k → Trie v V ∞ → Trie v (eat V (k ∷ [])) ∞
  lookupTrie k t = t Maybe.>>= Trie⁺.lookupTrie⁺ k

------------------------------------------------------------------------
-- Construction

  empty : Trie v V ∞
  empty = nothing

  singleton : ∀ ks → Val ks → Trie v V ∞
  singleton ks v = just (Trie⁺.singleton ks v)

  insertWith : ∀ ks → (Maybe (Val ks) → Val ks) → Trie v V ∞ → Trie v V ∞
  insertWith ks f (just t) = just (Trie⁺.insertWith ks f t)
  insertWith ks f nothing  = singleton ks (f nothing)

  insert : ∀ ks → Val ks → Trie v V ∞ → Trie v V ∞
  insert ks = insertWith ks ∘′ const

  fromList : List (∃ Val) → Trie v V ∞
  fromList = Maybe.map Trie⁺.fromList⁺ ∘′ List⁺.fromList

  toList : ∀ {i} → Trie⁺ v V i → List (∃ Val)
  toList = List⁺.toList ∘′ Trie⁺.toList⁺

------------------------------------------------------------------------
-- Modification

module _ {v} {V : Value ≋-setoid (v ⊔ k ⊔ e ⊔ r)}
         {w} {W : Value ≋-setoid (w ⊔ k ⊔ e ⊔ r)}
         where

  private
    Val = Value.family V
    Wal = Value.family W

  map : ∀ {i} → ∀[ Val ⇒ Wal ] → Trie v V i → Trie w W i
  map = Maybe.map ∘′ Trie⁺.map v w V W

-- Deletion

module _ {v} {V : Value ≋-setoid (v ⊔ k ⊔ e ⊔ r)} where

  -- Use a function to decide how to modify the sub-Trie⁺ whose root is
  -- at the end of path ks.
  deleteWith : ∀ {i} (ks : Word) →
     (∀ {i} → Trie⁺ v (eat V ks) i → Maybe (Trie⁺ v (eat V ks) i)) →
     Trie v V i → Trie v V i
  deleteWith ks f t = t Maybe.>>= Trie⁺.deleteWith ks f

  -- Remove the whole node
  deleteTrie⁺ : ∀ {i} (ks : Word) → Trie v V i → Trie v V i
  deleteTrie⁺ ks t = t Maybe.>>= Trie⁺.deleteTrie⁺ ks

  -- Remove the value and keep the sub-Tries (if any)
  deleteValue : ∀ {i} (ks : Word) → Trie v V i → Trie v V i
  deleteValue ks t = t Maybe.>>= Trie⁺.deleteValue ks

  -- Remove the sub-Tries and keep the value (if any)
  deleteTries⁺ : ∀ {i} (ks : Word) → Trie v V i → Trie v V i
  deleteTries⁺ ks t = t Maybe.>>= Trie⁺.deleteTries⁺ ks
