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
    l u : Key⁺

module _ {V : Value v}
         {P : Pred (K& V) p}
         (k : Key) (v : Value.family V k) (l<k<u : l < k < u)
         where

  singleton⁺ : P (k , v) → Any P (singleton k v l<k<u)
  singleton⁺ Pkv = here Pkv

  singleton⁻ : Any P (singleton k v l<k<u) → P (k , v)
  singleton⁻ (here Pkv) = Pkv
