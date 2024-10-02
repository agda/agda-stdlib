------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of refinement types
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Refinement.Properties where

open import Level
open import Data.Refinement
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary.Recomputable

private
  variable
    a p : Level
    A : Set a

module _ {P : A → Set p} where

  value-injective : {v w : Refinement A P} → value v ≡ value w → v ≡ w
  value-injective refl = refl
