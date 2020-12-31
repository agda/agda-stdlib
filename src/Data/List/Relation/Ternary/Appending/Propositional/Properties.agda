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
import Data.List.Relation.Ternary.Appending.Properties as Appendingₚ
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; module ≡-Reasoning)

private
  variable
    as bs cs ds : List A

[]++⁻¹ : Appending [] bs cs → bs ≡ cs
[]++⁻¹ ([]++ rs) = Pw.Pointwise-≡⇒≡ rs

++[]⁻¹ : Appending as [] cs → as ≡ cs
++[]⁻¹ {as} {cs} ls = begin
  as            ≡˘⟨ Listₚ.++-identityʳ as ⟩
  as List.++ [] ≡⟨ break ls ⟩
  cs            ∎ where open ≡-Reasoning

trans : Appending as bs cs → cs ≋ ds → Appending as bs ds
trans = Appendingₚ.transitive Eq.trans Eq.trans

Appending-conicalˡ : Appending as bs [] → as ≡ []
Appending-conicalˡ ([]++ rs) = refl

Appending-conicalʳ : Appending as bs [] → bs ≡ []
Appending-conicalʳ ([]++ rs) = Pw.Pointwise-≡⇒≡ rs
