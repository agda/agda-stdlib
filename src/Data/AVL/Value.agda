------------------------------------------------------------------------
-- The Agda standard library
--
-- Values for AVL trees
-- Values must respect the underlying equivalence on keys
-----------------------------------------------------------------------

open import Relation.Binary using (Rel; IsEquivalence)

module Data.AVL.Value {k e} {Key : Set k} {_≈_ : Rel Key e} (S : IsEquivalence _≈_) where

open import Level
import Function as F
open import Relation.Binary using (_Respects_)

record Value v : Set (k ⊔ e ⊔ Level.suc v) where
  constructor MkValue
  field family   : Key → Set v
        respects : family Respects _≈_

const : ∀ {v} → Set v → Value v
Value.family   (const V) = F.const V
Value.respects (const V) = F.const F.id
