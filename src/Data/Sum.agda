------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Sum where

open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Level
import Relation.Nullary.Decidable.Core as Dec

private
  variable
    a b : Level
    A B : Set a

------------------------------------------------------------------------
-- Re-export content from base module

open import Data.Sum.Base public

------------------------------------------------------------------------
-- Additional functions

module _ {A : Set a} {B : Set b} where

  isInj₁ : A ⊎ B → Maybe A
  isInj₁ (inj₁ x) = just x
  isInj₁ (inj₂ y) = nothing

  isInj₂ : A ⊎ B → Maybe B
  isInj₂ (inj₁ x) = nothing
  isInj₂ (inj₂ y) = just y

  From-inj₁ : A ⊎ B → Set a
  From-inj₁ (inj₁ _) = A
  From-inj₁ (inj₂ _) = ⊤

  from-inj₁ : (x : A ⊎ B) → From-inj₁ x
  from-inj₁ (inj₁ x) = x
  from-inj₁ (inj₂ _) = _

  From-inj₂ : A ⊎ B → Set b
  From-inj₂ (inj₁ _) = ⊤
  From-inj₂ (inj₂ _) = B

  from-inj₂ : (x : A ⊎ B) → From-inj₂ x
  from-inj₂ (inj₁ _) = _
  from-inj₂ (inj₂ x) = x

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.1

open Dec public using (fromDec; toDec)

