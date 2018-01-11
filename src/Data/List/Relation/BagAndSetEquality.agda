------------------------------------------------------------------------
-- The Agda standard library
--
-- Bag and set equality
------------------------------------------------------------------------

module Data.List.Relation.BagAndSetEquality where

open import Data.List
open import Data.List.Any
open import Data.List.Any.Properties using (Any↔)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (∃; _×_)
open import Function.Related as Related hiding (_∼[_]_)
open Related.EquationalReasoning
open import Relation.Binary using (Preorder; Setoid)
open import Function.Inverse as Inv using (_↔_; module Inverse)

------------------------------------------------------------------------
-- Definitions

open Related public using (Kind; Symmetric-kind) renaming
  ( implication         to subset
  ; reverse-implication to superset
  ; equivalence         to set
  ; injection           to subbag
  ; reverse-injection   to superbag
  ; bijection           to bag
  )

[_]-Order : Kind → ∀ {a} → Set a → Preorder _ _ _
[ k ]-Order A = Related.InducedPreorder₂ k {A = A} _∈_

[_]-Equality : Symmetric-kind → ∀ {a} → Set a → Setoid _ _
[ k ]-Equality A = Related.InducedEquivalence₂ k {A = A} _∈_

infix 4 _∼[_]_

_∼[_]_ : ∀ {a} {A : Set a} → List A → Kind → List A → Set _
_∼[_]_ {A = A} xs k ys = Preorder._∼_ ([ k ]-Order A) xs ys
