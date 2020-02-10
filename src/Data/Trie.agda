------------------------------------------------------------------------
-- The Agda standard library
--
-- Trie, basic type and operations
------------------------------------------------------------------------

-- See README.Data.Trie.NonDependent for an example of using a trie to
-- build a lexer.

{-# OPTIONS --without-K --safe --sized-types #-}

open import Relation.Binary using (Rel; StrictTotalOrder)

module Data.Trie {k e r} (S : StrictTotalOrder k e r) where

open import Level
open import Size
open import Data.List.Base using (List; []; _∷_; _++_)
import Data.List.NonEmpty as List⁺
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; maybe′)
open import Data.Product as Prod using (∃)
open import Data.These.Base as These using (These)
open import Function
open import Relation.Unary using (IUniversal; _⇒_)

open StrictTotalOrder S
  using (module Eq)
  renaming (Carrier to Key)

open import Data.List.Relation.Binary.Equality.Setoid Eq.setoid
open import Data.AVL.Value ≋-setoid using (Value)

------------------------------------------------------------------------
-- Definition

-- Trie is defined in terms of Trie⁺, the type of non-empty trie. This
-- guarantees that the trie is minimal: each path in the tree leads to
-- either a value or a number of non-empty sub-tries.

open import Data.Trie.NonEmpty S as Trie⁺ public
  using (Trie⁺; Tries⁺; Word; eat)

Trie : ∀ {v} (V : Value v) → Size → Set (v ⊔ k ⊔ e ⊔ r)
Trie V i = Maybe (Trie⁺ V i)

------------------------------------------------------------------------
-- Operations

-- Functions acting on Trie are wrappers for functions acting on Tries.
-- Sometimes the empty case is handled in a special way (e.g. insertWith
-- calls singleton when faced with an empty Trie).

module _ {v} {V : Value v} where

  private Val = Value.family V

------------------------------------------------------------------------
-- Lookup

  lookup : ∀ ks → Trie V ∞ → Maybe (These (Val ks) (Tries⁺ (eat V ks) ∞))
  lookup ks t = t Maybe.>>= Trie⁺.lookup ks

  lookupValue : ∀ ks → Trie V ∞ → Maybe (Val ks)
  lookupValue ks t = t Maybe.>>= Trie⁺.lookupValue ks

  lookupTries⁺ : ∀ ks → Trie V ∞ → Maybe (Tries⁺ (eat V ks) ∞)
  lookupTries⁺ ks t = t Maybe.>>= Trie⁺.lookupTries⁺ ks

  lookupTrie : ∀ k → Trie V ∞ → Trie (eat V (k ∷ [])) ∞
  lookupTrie k t = t Maybe.>>= Trie⁺.lookupTrie⁺ k

------------------------------------------------------------------------
-- Construction

  empty : Trie V ∞
  empty = nothing

  singleton : ∀ ks → Val ks → Trie V ∞
  singleton ks v = just (Trie⁺.singleton ks v)

  insertWith : ∀ ks → (Maybe (Val ks) → Val ks) → Trie V ∞ → Trie V ∞
  insertWith ks f (just t) = just (Trie⁺.insertWith ks f t)
  insertWith ks f nothing  = singleton ks (f nothing)

  insert : ∀ ks → Val ks → Trie V ∞ → Trie V ∞
  insert ks = insertWith ks ∘′ const

  fromList : List (∃ Val) → Trie V ∞
  fromList = Maybe.map Trie⁺.fromList⁺ ∘′ List⁺.fromList

  toList : Trie V ∞ → List (∃ Val)
  toList (just t) = List⁺.toList (Trie⁺.toList⁺ t)
  toList nothing  = []

------------------------------------------------------------------------
-- Modification

module _ {v w} {V : Value v} {W : Value w} where

  private
    Val = Value.family V
    Wal = Value.family W

  map : ∀ {i} → ∀[ Val ⇒ Wal ] → Trie V i → Trie W i
  map = Maybe.map ∘′ Trie⁺.map V W

-- Deletion

module _ {v} {V : Value v} where

  -- Use a function to decide how to modify the sub-Trie⁺ whose root is
  -- at the end of path ks.
  deleteWith : ∀ {i} (ks : Word) →
     (∀ {i} → Trie⁺ (eat V ks) i → Maybe (Trie⁺ (eat V ks) i)) →
     Trie V i → Trie V i
  deleteWith ks f t = t Maybe.>>= Trie⁺.deleteWith ks f

  -- Remove the whole node
  deleteTrie⁺ : ∀ {i} (ks : Word) → Trie V i → Trie V i
  deleteTrie⁺ ks t = t Maybe.>>= Trie⁺.deleteTrie⁺ ks

  -- Remove the value and keep the sub-Tries (if any)
  deleteValue : ∀ {i} (ks : Word) → Trie V i → Trie V i
  deleteValue ks t = t Maybe.>>= Trie⁺.deleteValue ks

  -- Remove the sub-Tries and keep the value (if any)
  deleteTries⁺ : ∀ {i} (ks : Word) → Trie V i → Trie V i
  deleteTries⁺ ks t = t Maybe.>>= Trie⁺.deleteTries⁺ ks
