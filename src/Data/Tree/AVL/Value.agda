------------------------------------------------------------------------
-- The Agda standard library
--
-- Values for AVL trees
-- Values must respect the underlying equivalence on keys
-----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; _Respects_)

module Data.Tree.AVL.Value {a ℓ} (S : Setoid a ℓ) where

open import Data.Product using (Σ; _,_)
open import Level using (suc; _⊔_)
import Function as F
open Setoid S renaming (Carrier to Key)

-----------------------------------------------------------------------
-- A Value

record Value v : Set (a ⊔ ℓ ⊔ suc v) where
  constructor MkValue
  field
    family   : Key → Set v
    respects : family Respects _≈_

-----------------------------------------------------------------------
-- A Key together with its value

record K&_ {v} (V : Value v) : Set (a ⊔ v) where
  constructor _,_
  field
    key   : Key
    value : Value.family V key
open K&_ public

module _ {v} {V : Value v} where

  toPair : K& V → Σ Key (Value.family V)
  toPair (k , v) = k , v

  fromPair : Σ Key (Value.family V) → K& V
  fromPair (k , v) = k , v

-----------------------------------------------------------------------
-- The constant family of values

-- The function `const` is defined using copatterns to prevent eager
-- unfolding of the function in goal types.
const : ∀ {v} → Set v → Value v
Value.family   (const V) = F.const V
Value.respects (const V) = F.const F.id
