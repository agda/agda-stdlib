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

isInj₁ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Maybe A
isInj₁ (inj₁ x) = just x
isInj₁ (inj₂ y) = nothing

isInj₂ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Maybe B
isInj₂ (inj₁ x) = nothing
isInj₂ (inj₂ y) = just y

From-inj₁ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Set a
From-inj₁ {A = A} (inj₁ _) = A
From-inj₁         (inj₂ _) = Lift ⊤

from-inj₁ : ∀ {a b} {A : Set a} {B : Set b} (x : A ⊎ B) → From-inj₁ x
from-inj₁ (inj₁ x) = x
from-inj₁ (inj₂ _) = lift tt

From-inj₂ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Set b
From-inj₂         (inj₁ _) = Lift ⊤
From-inj₂ {B = B} (inj₂ _) = B

from-inj₂ : ∀ {a b} {A : Set a} {B : Set b} (x : A ⊎ B) → From-inj₂ x
from-inj₂ (inj₁ _) = lift tt
from-inj₂ (inj₂ x) = x
