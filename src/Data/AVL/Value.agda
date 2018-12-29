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

-- The function `const` is defined using copatterns to prevent eager
-- unfolding of the function in goal types.
const : ∀ {v} → Set v → Value v
Value.family   (const V) = F.const V
Value.respects (const V) = F.const F.id
