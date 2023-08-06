------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite maps with indexed keys and values, based on AVL trees
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Product as Prod
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong; subst)
import Data.Tree.AVL.Value

module Data.Tree.AVL.IndexedMap
  {i k v ℓ}
  {Index : Set i} {Key : Index → Set k}  (Value : Index → Set v)
  {_<_ : Rel (∃ Key) ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

import Data.Tree.AVL
open import Data.Bool.Base using (Bool)
open import Data.List.Base as List using (List)
open import Data.Maybe.Base as Maybe using (Maybe)
open import Data.Nat.Base using (ℕ)
open import Function.Base
open import Level using (Level; _⊔_)

private
  variable
    a : Level
    A : Set a

-- Key/value pairs.

KV : Set (i ⊔ k ⊔ v)
KV = ∃ λ i → Key i × Value i

-- Conversions.

private

  fromKV : KV → Σ[ ik ∈ ∃ Key ] Value (proj₁ ik)
  fromKV (i , k , v) = ((i , k) , v)

  toKV : Σ[ ik ∈ ∃ Key ] Value (proj₁ ik) → KV
  toKV ((i , k) , v) = (i , k , v)

-- The map type.

private
  open module AVL =
    Data.Tree.AVL (record { isStrictTotalOrder = isStrictTotalOrder })
    using () renaming (Tree to Map′)

Map = Map′ (AVL.MkValue (Value ∘ proj₁) (subst Value ∘′ cong proj₁))

-- Repackaged functions.

empty : Map
empty = AVL.empty

singleton : ∀ {i} → Key i → Value i → Map
singleton k v = AVL.singleton (-, k) v

insert : ∀ {i} → Key i → Value i → Map → Map
insert k v = AVL.insert (-, k) v

delete : ∀ {i} → Key i → Map → Map
delete k = AVL.delete (-, k)

lookup : ∀ {i} → Map → Key i → Maybe (Value i)
lookup m k = AVL.lookup m (-, k)

member : ∀ {i} → Key i → Map → Bool
member k = AVL.member (-, k)

headTail : Map → Maybe (KV × Map)
headTail m = Maybe.map (Prod.map₁ (toKV ∘′ AVL.toPair)) (AVL.headTail m)

initLast : Map → Maybe (Map × KV)
initLast m = Maybe.map (Prod.map₂ (toKV ∘′ AVL.toPair)) (AVL.initLast m)

foldr : (∀ {k} → Value k → A → A) → A → Map → A
foldr cons = AVL.foldr cons

fromList : List KV → Map
fromList = AVL.fromList ∘ List.map (AVL.fromPair ∘′ fromKV)

toList : Map → List KV
toList = List.map (toKV ∘′ AVL.toPair) ∘ AVL.toList

size : Map → ℕ
size = AVL.size


------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

infixl 4 _∈?_
_∈?_ : ∀ {i} → Key i → Map → Bool
_∈?_ = member
{-# WARNING_ON_USAGE _∈?_
"Warning: _∈?_ was deprecated in v2.0.
Please use member instead."
#-}
