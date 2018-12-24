------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.AbelianGroup
         {g₁ g₂} (G : AbelianGroup g₁ g₂) where

open AbelianGroup G
open import Function
open import Relation.Binary.Reasoning.Equational setoid

------------------------------------------------------------------------
-- Publicly re-export group properties

open import Algebra.Properties.Group group public

------------------------------------------------------------------------
-- Properties of abelian groups

private

  lemma₁ : ∀ x y → x ∙ y ∙ x ⁻¹ ≈ y
  lemma₁ x y = begin
    x ∙ y ∙ x ⁻¹    ≈⟨ ∙-congˡ $ comm _ _ ⟩
    y ∙ x ∙ x ⁻¹    ≈⟨ assoc _ _ _ ⟩
    y ∙ (x ∙ x ⁻¹)  ≈⟨ ∙-congʳ $ inverseʳ _ ⟩
    y ∙ ε           ≈⟨ identityʳ _ ⟩
    y               ∎

  lemma₂ : ∀ x y → x ∙ (y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹) ≈ y ⁻¹
  lemma₂ x y = begin
    x ∙ (y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹)  ≈⟨ sym $ assoc _ _ _ ⟩
    x ∙ (y ∙ (x ∙ y) ⁻¹) ∙ y ⁻¹  ≈⟨ ∙-congˡ $ sym $ assoc _ _ _ ⟩
    x ∙ y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹    ≈⟨ ∙-congˡ $ inverseʳ _ ⟩
    ε ∙ y ⁻¹                     ≈⟨ identityˡ _ ⟩
    y ⁻¹                         ∎

⁻¹-∙-comm : ∀ x y → x ⁻¹ ∙ y ⁻¹ ≈ (x ∙ y) ⁻¹
⁻¹-∙-comm x y = begin
  x ⁻¹ ∙ y ⁻¹                         ≈⟨ comm _ _ ⟩
  y ⁻¹ ∙ x ⁻¹                         ≈⟨ ∙-congˡ $ sym $ (lemma₂ x y) ⟩
  x ∙ (y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹) ∙ x ⁻¹  ≈⟨ lemma₁ _ _ ⟩
  y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹               ≈⟨ lemma₁ _ _ ⟩
  (x ∙ y) ⁻¹                          ∎
  where

