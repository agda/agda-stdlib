------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversions for surjections
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties.Surjection where

open import Function.Base
open import Function.Definitions
open import Function.Bundles
open import Level using (Level)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

private
  variable
    a b ℓ : Level
    A B : Set a
    T S : Setoid a ℓ

injective⇒to⁻-cong : (surj : Surjection S T) →
                      (open Surjection surj) →
                      Injective Eq₁._≈_ Eq₂._≈_ to →
                      Congruent Eq₂._≈_ Eq₁._≈_ to⁻
injective⇒to⁻-cong {T = T} surj injective {x} {y} x≈y = injective $ begin
  to (to⁻ x) ≈⟨ to∘to⁻ x ⟩
  x          ≈⟨ x≈y ⟩
  y          ≈˘⟨ to∘to⁻ y ⟩
  to (to⁻ y) ∎
  where
  open SetoidReasoning T
  open Surjection surj
  to∘to⁻ = proj₂ ∘ strictlySurjective

------------------------------------------------------------------------
-- Conversion functions

↠⇒↪ : A ↠ B → B ↪ A
↠⇒↪ s = mk↪ {from = to} λ { refl → proj₂ (strictlySurjective _)}
  where open Surjection s

↠⇒⇔ : A ↠ B → A ⇔ B
↠⇒⇔ s = mk⇔ to (proj₁ ∘ surjective)
  where open Surjection s
