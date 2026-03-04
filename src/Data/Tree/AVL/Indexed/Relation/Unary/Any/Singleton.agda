------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of singleton related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Singleton
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Level using (Level)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any
open StrictTotalOrder sto renaming (Carrier to Key)

private
  variable
    v p : Level
    V : Value v
    l u : Key⁺
    P : Pred (K& V) p

module _ {V : Value v} where

  private
    Val  = Value.family V

  singleton⁺ : {P : Pred (K& V) p} →
               (k : Key) →
               (v : Val k) →
               (l<k<u : l < k < u) →
               P (k , v) → Any P (singleton k v l<k<u)
  singleton⁺ k v l<k<u Pkv = here Pkv

  singleton⁻ : {P : Pred (K& V) p} →
               (k : Key) →
               (v : Val k) →
               (l<k<u : l < k < u) →
               Any P (singleton k v l<k<u) → P (k , v)
  singleton⁻ k v l<k<u (here Pkv) = Pkv
