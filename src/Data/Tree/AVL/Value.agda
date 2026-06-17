------------------------------------------------------------------------
-- The Agda standard library
--
-- Values for AVL trees
-- Values must respect the underlying equivalence on keys
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.Tree.AVL.Value {a ℓ} (S : Setoid a ℓ) where

open import Data.Product.Base using (Σ; _,_)
open import Level using (Level; suc; _⊔_)
import Function.Base as Function
open import Relation.Binary.Definitions using (_Respects_)

open Setoid S using (_≈_) renaming (Carrier to Key)

private
  variable
    v : Level


------------------------------------------------------------------------
-- A Value

record Value v : Set (a ⊔ ℓ ⊔ suc v) where
  constructor MkValue
  field
    family   : Key → Set v
    respects : family Respects _≈_

open Value using (family)

------------------------------------------------------------------------
-- A Key together with its value

record K&_ (V : Value v) : Set (a ⊔ v) where
  constructor _,_
  field
    key   : Key
    value : family V key
infixr 4 _,_
open K&_ public

module _ {V : Value v} where

  toPair : K& V → Σ Key (family V)
  toPair (k , v) = k , v

  fromPair : Σ Key (family V) → K& V
  fromPair (k , v) = k , v

------------------------------------------------------------------------
-- The constant family of values

-- The function `const` is defined using copatterns to prevent eager
-- unfolding of the function in goal types.
const : Set v → Value v
Value.family   (const V) = Function.const V
Value.respects (const V) = Function.const Function.id
