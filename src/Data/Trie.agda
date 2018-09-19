------------------------------------------------------------------------
-- The Agda standard library
--
-- Trie, basic type and operations
------------------------------------------------------------------------

open import Relation.Binary using (Rel; IsStrictTotalOrder)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

module Data.Trie
  {k r} {Key : Set k} {_<_ : Rel Key r}
  (S : IsStrictTotalOrder _≡_ _<_) where

open import Level
open import Size
open import Data.List.Base using (List; []; _++_)
import Data.List.NonEmpty as List⁺
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Product as Prod using (∃)
open import Data.These as These using (These)
open import Function
open import Relation.Unary using (IUniversal; _⇒_)

-- Trie is defined in terms of Trie⁺, the type of non-empty trie. This guarantees
-- that the trie is minimal: each path in the tree leads to either a value or a
-- number of non-empty sub-tries.

open import Data.Trie.NonEmpty S as Trie⁺ using (Trie⁺; Tries⁺; Word) public

Trie : ∀ {v} → (Word → Set v) → Size → Set (k ⊔ r ⊔ v)
Trie V i = Maybe (Trie⁺ V i)

-- Functions acting on Trie are wrappers for functions acting on Tries.
-- Sometimes the empty case is handled in a special way (e.g. insertWith
-- calls singleton when faced with an empty Trie).

module _ {v} {V : Word → Set v} where

-- Lookup

  lookup : ∀ ks → Trie V ∞ → Maybe (These (V ks) (Tries⁺ (V ∘′ (ks ++_)) ∞))
  lookup ks t = t Maybe.>>= Trie⁺.lookup ks

  lookupValue : ∀ ks → Trie V ∞ → Maybe (V ks)
  lookupValue ks t = t Maybe.>>= Trie⁺.lookupValue ks

  lookupTries⁺ : ∀ ks → Trie V ∞ → Maybe (Tries⁺ (V ∘′ (ks ++_)) ∞)
  lookupTries⁺ ks t = t Maybe.>>= Trie⁺.lookupTries⁺ ks

-- Construction

  empty : Trie V ∞
  empty = nothing

  singleton : ∀ ks → V ks → Trie V ∞
  singleton ks v = just (Trie⁺.singleton ks v)

  insertWith : ∀ ks → (Maybe (V ks) → V ks) → Trie V ∞ → Trie V ∞
  insertWith ks f (just t) = just (Trie⁺.insertWith ks f t)
  insertWith ks f nothing  = singleton ks (f nothing)

  insert : ∀ ks → V ks → Trie V ∞ → Trie V ∞
  insert ks = insertWith ks ∘′ const

  fromList : List (∃ V) → Trie V ∞
  fromList = Maybe.map Trie⁺.fromList⁺ ∘′ List⁺.fromList

  toList : ∀ {i} → Trie⁺ V i → List (∃ V)
  toList = List⁺.toList ∘′ Trie⁺.toList⁺

  map : ∀ {w} {W : Word → Set w} {i} → ∀[ V ⇒ W ] → Trie V i → Trie W i
  map = Maybe.map ∘′ Trie⁺.map
