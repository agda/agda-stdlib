------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Properties.AbelianGroup
         {g₁ g₂} (G : AbelianGroup g₁ g₂) where

import Algebra.Properties.Group as GP
open import Function
import Relation.Binary.EqReasoning as EqR

open AbelianGroup G
open EqR setoid

open GP group public

private
  lemma₁ : ∀ x y → x ∙ y ∙ x ⁻¹ ≈ y
  lemma₁ x y = begin
    x ∙ y ∙ x ⁻¹    ≈⟨ comm _ _ ⟨ ∙-cong ⟩ refl ⟩
    y ∙ x ∙ x ⁻¹    ≈⟨ assoc _ _ _ ⟩
    y ∙ (x ∙ x ⁻¹)  ≈⟨ refl ⟨ ∙-cong ⟩ inverseʳ _ ⟩
    y ∙ ε           ≈⟨ identityʳ _ ⟩
    y               ∎

  lemma₂ : ∀ x y → x ∙ (y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹) ≈ y ⁻¹
  lemma₂ x y = begin
    x ∙ (y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹)  ≈⟨ sym $ assoc _ _ _ ⟩
    x ∙ (y ∙ (x ∙ y) ⁻¹) ∙ y ⁻¹  ≈⟨ sym $ assoc _ _ _ ⟨ ∙-cong ⟩ refl ⟩
    x ∙ y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹    ≈⟨ inverseʳ _ ⟨ ∙-cong ⟩ refl ⟩
    ε ∙ y ⁻¹                     ≈⟨ identityˡ _ ⟩
    y ⁻¹                         ∎

⁻¹-∙-comm : ∀ x y → x ⁻¹ ∙ y ⁻¹ ≈ (x ∙ y) ⁻¹
⁻¹-∙-comm x y = begin
  x ⁻¹ ∙ y ⁻¹                         ≈⟨ comm _ _ ⟩
  y ⁻¹ ∙ x ⁻¹                         ≈⟨ sym $ (lemma₂ x y) ⟨ ∙-cong ⟩ refl ⟩
  x ∙ (y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹) ∙ x ⁻¹  ≈⟨ lemma₁ _ _ ⟩
  y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹               ≈⟨ lemma₁ _ _ ⟩
  (x ∙ y) ⁻¹                          ∎
  where

