------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of vector's Any
------------------------------------------------------------------------

module Data.Vec.Any.Properties where

open import Data.Vec
open import Data.Vec.Any
open import Relation.Unary

module _ {a} {A : Set a} {p} {P : Pred A p} where

  lookup-index : ∀ {m} {xs : Vec A m} (p : Any P xs) → P (lookup (index p) xs)
  lookup-index (here px) = px
  lookup-index (there p) = lookup-index p
