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
open import Data.List.Relation.Ternary.Appending.Propositional {A = A}
open import Relation.Binary.PropositionalEquality using (_≡_; module ≡-Reasoning)

private
  variable
    as bs cs : List A

[]++⁻¹ : Appending [] bs cs → bs ≡ cs
[]++⁻¹ ([]++ bcs) = Pw.Pointwise-≡⇒≡ bcs

++[]⁻¹ : Appending as [] cs → as ≡ cs
++[]⁻¹ {as} {cs} rs = begin
  as            ≡˘⟨ Listₚ.++-identityʳ as ⟩
  as List.++ [] ≡⟨ break rs ⟩
  cs            ∎ where open ≡-Reasoning
