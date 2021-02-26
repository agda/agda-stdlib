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

xyx⁻¹≈y : ∀ x y → x ∙ y ∙ x ⁻¹ ≈ y
xyx⁻¹≈y x y = begin
  x ∙ y ∙ x ⁻¹    ≈⟨ ∙-congʳ $ comm _ _ ⟩
  y ∙ x ∙ x ⁻¹    ≈⟨ assoc _ _ _ ⟩
  y ∙ (x ∙ x ⁻¹)  ≈⟨ ∙-congˡ $ inverseʳ _ ⟩
  y ∙ ε           ≈⟨ identityʳ _ ⟩
  y               ∎

⁻¹-distrib-∙ : ∀ x y → (x ∙ y) ⁻¹ ≈ x ⁻¹ ∙ y ⁻¹
⁻¹-distrib-∙ x y = sym $ begin
  x ⁻¹ ∙ y ⁻¹ ≈˘⟨ ⁻¹-anti-homo-∙ y x ⟩
  (y ∙ x) ⁻¹  ≈⟨ ⁻¹-cong $ comm y x ⟩
  (x ∙ y) ⁻¹  ∎


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.6

⁻¹-∙-comm : ∀ x y → x ⁻¹ ∙ y ⁻¹ ≈ (x ∙ y) ⁻¹
⁻¹-∙-comm x y = sym (⁻¹-distrib-∙ x y)
{-# WARNING_ON_USAGE ⁻¹-∙-comm
"Warning: ⁻¹-∙-comm was deprecated in v1.6.
Please use ⁻¹-distrib-∙ instead.
NOTE: the equality is flipped so you will need sym (⁻¹-distrib-∙ ...)."
#-}
