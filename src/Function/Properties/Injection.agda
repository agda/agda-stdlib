------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties for injections
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties.Injection where

open import Function.Base
open import Function.Definitions
open import Function.Bundles
import Function.Construct.Identity as Identity
import Function.Construct.Composition as Compose
open import Level using (Level)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

private
  variable
    a b ℓ : Level
    A B : Set a
    T S U : Setoid a ℓ

------------------------------------------------------------------------
-- Constructors

mkInjection : (f : Func S T) (open Func f) →
              Injective Eq₁._≈_ Eq₂._≈_ to  →
              Injection S T
mkInjection f injective = record
  { Func f
  ; injective = injective
  }

------------------------------------------------------------------------
-- Conversion functions

↣⇒⟶ : A ↣ B → A ⟶ B
↣⇒⟶ = Injection.function

------------------------------------------------------------------------
-- Properties

↣-refl : Injection S S
↣-refl = Identity.injection _

↣-trans : Injection S T → Injection T U → Injection S U
↣-trans = Compose.injection
