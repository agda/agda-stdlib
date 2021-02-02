------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of list appending
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Ternary.Appending.Propositional.Properties {a} {A : Set a} where

open import Data.List.Base as List using (List; [])
import Data.List.Properties as Listₚ
import Data.List.Relation.Binary.Pointwise as Pw
open import Data.List.Relation.Binary.Equality.Propositional using (_≋_)
open import Data.List.Relation.Ternary.Appending.Propositional {A = A}
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; setoid)

import Data.List.Relation.Ternary.Appending.Setoid.Properties (setoid A)
  as Appendingₚ

private
  variable
    as bs cs : List A

------------------------------------------------------------------------
-- Re-export existing properties

open Appendingₚ public
  hiding ([]++⁻¹; ++[]⁻¹)

------------------------------------------------------------------------
-- Prove propositional-specific ones

[]++⁻¹ : Appending [] bs cs → bs ≡ cs
[]++⁻¹ = Pw.Pointwise-≡⇒≡ ∘′ Appendingₚ.[]++⁻¹

++[]⁻¹ : Appending as [] cs → as ≡ cs
++[]⁻¹ = Pw.Pointwise-≡⇒≡ ∘′ Appendingₚ.++[]⁻¹
