-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the homogeneous sublist relation
------------------------------------------------------------------------

module Data.List.Relation.Sublist.Homogeneous.Properties where

open import Data.List.Base using (List; []; _∷_; takeWhile; dropWhile; filter)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Sublist.Heterogeneous
open import Data.List.Relation.Sublist.Heterogeneous.Properties public

open import Function
open import Relation.Unary as U using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬?)

module _ {a r p} {A : Set a} {R : Rel A r} {P : Pred A p} (P? : U.Decidable P) where

  takeWhile-Sublist-filter : ∀ {as} → Pointwise R as as →
    Sublist R (takeWhile P? as) (filter P? as)
  takeWhile-Sublist-filter [] = []
  takeWhile-Sublist-filter {a ∷ as} (p ∷ ps) with P? a
  ... | yes pa = p ∷ takeWhile-Sublist-filter ps
  ... | no ¬pa = minimum _

  filter-Sublist-dropWhile : ∀ {as} → Pointwise R as as →
    Sublist R (filter P? as) (dropWhile (¬? ∘ P?) as)
  filter-Sublist-dropWhile [] = []
  filter-Sublist-dropWhile {a ∷ as} (p ∷ ps) with P? a
  ... | yes pa = p ∷ filter-Sublist P? ps
  ... | no ¬pa = filter-Sublist-dropWhile ps
