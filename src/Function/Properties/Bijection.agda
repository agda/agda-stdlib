------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversions for bijections
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties.Bijection where

open import Function.Bundles
open import Level using (Level)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Data.Product using (_,_; proj₁; proj₂)
open import Function.Properties.Inverse using (Inverse⇒Equivalence)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Conversion functions

module _ (A : Setoid a ℓ₁) (B : Setoid b ℓ₂) where

  Bijection⇒Inverse : Bijection A B → Inverse A B
  Bijection⇒Inverse b = record
    { f =     f
    ; f⁻¹ =   λ y → proj₁ (proj₂ bijective y)
    ; cong₁ = cong
    ; cong₂ = λ {x} {y} x≈y → proj₁ bijective (begin
        f (proj₁ (proj₂ bijective x)) ≈⟨ proj₂ (proj₂ bijective x) ⟩
        x                             ≈⟨ x≈y ⟩
        y                             ≈˘⟨ proj₂ (proj₂ bijective y) ⟩
        f (proj₁ (proj₂ bijective y)) ∎)
      ; inverse = (λ x → proj₂ (proj₂ bijective x)) , λ y → proj₁ bijective (proj₂ (proj₂ bijective (f y))) }
    where open SetoidReasoning B
          open Bijection b

  Bijection⇒Equivalence : Bijection A B → Equivalence A B
  Bijection⇒Equivalence b = Inverse⇒Equivalence A B (Bijection⇒Inverse b)


module _ {A : Set a} {B : Set b} where

  ⤖⇒↔ : A ⤖ B → A ↔ B
  ⤖⇒↔ = Bijection⇒Inverse (setoid A) (setoid B)

  ⤖⇒⇔ : A ⤖ B → A ⇔ B
  ⤖⇒⇔ = Bijection⇒Equivalence (setoid A) (setoid B)
