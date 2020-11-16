------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the homogeneous infix relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Infix.Homogeneous.Properties where

open import Level
open import Function.Base using (_∘′_)
open import Relation.Binary

open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise)
open import Data.List.Relation.Binary.Infix.Heterogeneous
open import Data.List.Relation.Binary.Infix.Heterogeneous.Properties

private
  variable
    a b r s : Level
    A : Set a
    B : Set b
    R : REL A B r
    S : REL A B s

isPreorder : IsPreorder R S → IsPreorder (Pointwise R) (Infix S)
isPreorder po = record
  { isEquivalence = Pointwise.isEquivalence PO.isEquivalence
  ; reflexive     = fromPointwise ∘′ Pointwise.map PO.reflexive
  ; trans         = trans PO.trans
  } where module PO = IsPreorder po

isPartialOrder : IsPartialOrder R S → IsPartialOrder (Pointwise R) (Infix S)
isPartialOrder po = record
  { isPreorder = isPreorder PO.isPreorder
  ; antisym    = antisym PO.antisym
  } where module PO = IsPartialOrder po

isDecPartialOrder : IsDecPartialOrder R S → IsDecPartialOrder (Pointwise R) (Infix S)
isDecPartialOrder dpo = record
  { isPartialOrder = isPartialOrder DPO.isPartialOrder
  ; _≟_            = Pointwise.decidable DPO._≟_
  ; _≤?_           = infix? DPO._≤?_
  } where module DPO = IsDecPartialOrder dpo
