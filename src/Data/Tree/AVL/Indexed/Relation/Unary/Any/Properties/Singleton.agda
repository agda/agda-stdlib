------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of singleton related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Singleton
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Level using (Level)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any


private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p
    l u : Key⁺


module _ {V : Value v} (open Value V renaming (family to Val))
         k (v : Val k) (l<k<u : l < k < u) where

  singleton⁺ : P (k , v) → Any {V = V} P (singleton k v l<k<u)
  singleton⁺ Pkv = here Pkv

  singleton⁻ : Any {V = V} P (singleton k v l<k<u) → P (k , v)
  singleton⁻ (here Pkv) = Pkv
