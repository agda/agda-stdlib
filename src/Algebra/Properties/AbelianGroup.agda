------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.AbelianGroup
  {a ℓ} (G : AbelianGroup a ℓ) where

open AbelianGroup G
open import Function
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Publicly re-export group properties

open import Algebra.Properties.Group group public

------------------------------------------------------------------------
-- Properties of abelian groups

private
  lemma₂ : ∀ x y → x ∙ (y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹) ≈ y ⁻¹
  lemma₂ x y = begin
    x ∙ (y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹)  ≈˘⟨ assoc _ _ _ ⟩
    x ∙ (y ∙ (x ∙ y) ⁻¹) ∙ y ⁻¹  ≈˘⟨ ∙-congʳ $ assoc _ _ _ ⟩
    x ∙ y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹    ≈⟨  ∙-congʳ $ inverseʳ _ ⟩
    ε ∙ y ⁻¹                     ≈⟨  identityˡ _ ⟩
    y ⁻¹                         ∎

xyx⁻¹≈y : ∀ x y → x ∙ y ∙ x ⁻¹ ≈ y
xyx⁻¹≈y x y = begin
  x ∙ y ∙ x ⁻¹    ≈⟨ ∙-congʳ $ comm _ _ ⟩
  y ∙ x ∙ x ⁻¹    ≈⟨ assoc _ _ _ ⟩
  y ∙ (x ∙ x ⁻¹)  ≈⟨ ∙-congˡ $ inverseʳ _ ⟩
  y ∙ ε           ≈⟨ identityʳ _ ⟩
  y               ∎

⁻¹-∙-comm : ∀ x y → x ⁻¹ ∙ y ⁻¹ ≈ (x ∙ y) ⁻¹
⁻¹-∙-comm x y = begin
  x ⁻¹ ∙ y ⁻¹                         ≈⟨  comm _ _ ⟩
  y ⁻¹ ∙ x ⁻¹                         ≈˘⟨ ∙-congʳ $ lemma₂ x y ⟩
  x ∙ (y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹) ∙ x ⁻¹  ≈⟨  xyx⁻¹≈y x _ ⟩
  y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹               ≈⟨  xyx⁻¹≈y y _ ⟩
  (x ∙ y) ⁻¹                          ∎
