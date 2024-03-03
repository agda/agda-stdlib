------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of list appending
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Ternary.Appending.Propositional.Properties {a} {A : Set a} where

open import Data.List.Base as List using (List; [])
import Data.List.Relation.Binary.Pointwise as Pw using (Pointwise-≡⇒≡)
open import Data.List.Relation.Binary.Equality.Propositional using (_≋_)
open import Data.List.Relation.Ternary.Appending.Propositional {A = A}
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

import Data.List.Relation.Ternary.Appending.Setoid.Properties (setoid A)
  as Appending

private
  variable
    as bs cs : List A

------------------------------------------------------------------------
-- Re-export existing properties

open Appending public
  hiding ([]++⁻¹; ++[]⁻¹)

------------------------------------------------------------------------
-- Prove propositional-specific ones

[]++⁻¹ : Appending [] bs cs → bs ≡ cs
[]++⁻¹ = Pw.Pointwise-≡⇒≡ ∘′ Appending.[]++⁻¹

++[]⁻¹ : Appending as [] cs → as ≡ cs
++[]⁻¹ = Pw.Pointwise-≡⇒≡ ∘′ Appending.++[]⁻¹
