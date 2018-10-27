------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of vector's Any
------------------------------------------------------------------------

module Data.Vec.Any.Properties where

open import Data.Vec as Vec using (Vec; lookup)
open import Data.Vec.Any
open import Data.List.Any as LAny using (here; there)
open import Relation.Unary

module _ {a} {A : Set a} {p} {P : Pred A p} where

  lookup-index : ∀ {m} {xs : Vec A m} (p : Any P xs) → P (lookup (index p) xs)
  lookup-index (here px) = px
  lookup-index (there p) = lookup-index p

  fromList : ∀ {xs} → LAny.Any P xs → Any P (Vec.fromList xs)
  fromList (here px) = here px
  fromList (there v) = there (fromList v)

  toList : ∀ {n} {xs : Vec A n} → Any P xs → LAny.Any P (Vec.toList xs)
  toList (here px) = here px
  toList (there v) = there (toList v)
