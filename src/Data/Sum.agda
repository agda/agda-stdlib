------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums (disjoint unions)
------------------------------------------------------------------------

module Data.Sum where

open import Function
open import Data.Unit.Base using (⊤; tt)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Level
open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- Re-export content from base module

open import Data.Sum.Base public

------------------------------------------------------------------------
-- Additional functions

module _ {a b} {A : Set a} {B : Set b} where

  isInj₁ : A ⊎ B → Maybe A
  isInj₁ (inj₁ x) = just x
  isInj₁ (inj₂ y) = nothing

  isInj₂ : A ⊎ B → Maybe B
  isInj₂ (inj₁ x) = nothing
  isInj₂ (inj₂ y) = just y

  From-inj₁ : A ⊎ B → Set a
  From-inj₁ (inj₁ _) = A
  From-inj₁ (inj₂ _) = Lift a ⊤

  from-inj₁ : (x : A ⊎ B) → From-inj₁ x
  from-inj₁ (inj₁ x) = x
  from-inj₁ (inj₂ _) = _

  From-inj₂ : A ⊎ B → Set b
  From-inj₂ (inj₁ _) = Lift b ⊤
  From-inj₂ (inj₂ _) = B

  from-inj₂ : (x : A ⊎ B) → From-inj₂ x
  from-inj₂ (inj₁ _) = _
  from-inj₂ (inj₂ x) = x
