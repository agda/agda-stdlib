------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the sublist relation. This is commonly known
-- as Order Preserving Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional {a} {A : Set a} where

import Relation.Binary.PropositionalEquality as P
open import Relation.Unary using (Pred)

open import Data.List.Relation.Binary.Sublist.Setoid (P.setoid A) public
import Data.List.Relation.Binary.Sublist.Homogeneous.Properties as SubProp
open import Data.List.Relation.Unary.Any using (Any)

module _ {p} {P : Pred A p} where

  lookup : ∀ {xs ys} → xs ⊆ ys → Any P xs → Any P ys
  lookup = SubProp.lookup (P.subst _)
