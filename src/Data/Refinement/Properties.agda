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

private
  variable
    a p : Level
    A : Set a
    P : A → Set p
    v w : Refinement A P


------------------------------------------------------------------------
-- Basic properties

value-injective : value v ≡ value w → v ≡ w
value-injective refl = refl
