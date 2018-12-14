------------------------------------------------------------------------
-- The Agda standard library
--
-- Values for AVL trees
-- Values must respect the underlying equivalence on keys
-----------------------------------------------------------------------

open import Relation.Binary using (Setoid; _Respects_)

module Data.AVL.Value {a ℓ} (S : Setoid a ℓ) where

open import Level using (suc; _⊔_)
import Function as F
open Setoid S renaming (Carrier to Key)

record Value v : Set (a ⊔ ℓ ⊔ suc v) where
  constructor MkValue
  field
    family   : Key → Set v
    respects : family Respects _≈_

const : ∀ {v} → Set v → Value v
const V = record
  { family   = F.const V
  ; respects = F.const F.id
  }
