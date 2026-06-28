------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of All predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Relation.Unary.All.Properties where

open import Data.List.Fresh using (List#; []; _∷#_; _#[_]_; _#_)
open import Data.List.Fresh.Relation.Unary.All using (All; []; _∷_; append)
open import Data.Product.Base using (_,_)
open import Level using (Level)
open import Relation.Unary as Unary using (Pred)
open import Relation.Binary.Core using (Rel)

private
  variable
    a p r : Level
    A : Set a
    R : Rel A r
    P : Pred A p
    x : A
    xs ys : List# A R


fromAll : All (R x) xs → x #[ R ] xs
fromAll []       = _
fromAll (p ∷ ps) = p , fromAll ps

toAll : x #[ R ] xs → All (R x) xs
toAll {xs = []}      _        = []
toAll {xs = a ∷# as} (p , ps) = p ∷ toAll ps

append⁺ : ∀ {ps} → All P xs → All P ys → All P (append {R = R} xs ys ps)
append⁺ []         pys = pys
append⁺ (px ∷ pxs) pys = px ∷ append⁺ pxs pys
