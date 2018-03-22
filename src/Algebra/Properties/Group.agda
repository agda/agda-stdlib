------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Properties.Group {g₁ g₂} (G : Group g₁ g₂) where

open Group G
import Algebra.FunctionProperties as P; open P _≈_
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Function
open import Data.Product

⁻¹-involutive : ∀ x → x ⁻¹ ⁻¹ ≈ x
⁻¹-involutive x = begin
  x ⁻¹ ⁻¹               ≈⟨ sym $ identityʳ _ ⟩
  x ⁻¹ ⁻¹ ∙ ε           ≈⟨ refl ⟨ ∙-cong ⟩ sym (inverseˡ _) ⟩
  x ⁻¹ ⁻¹ ∙ (x ⁻¹ ∙ x)  ≈⟨ sym $ assoc _ _ _ ⟩
  x ⁻¹ ⁻¹ ∙ x ⁻¹ ∙ x    ≈⟨ inverseˡ _ ⟨ ∙-cong ⟩ refl ⟩
  ε ∙ x                 ≈⟨ identityˡ _ ⟩
  x                     ∎

private

  left-helper : ∀ x y → x ≈ (x ∙ y) ∙ y ⁻¹
  left-helper x y = begin
    x              ≈⟨ sym (identityʳ x) ⟩
    x ∙ ε          ≈⟨ refl ⟨ ∙-cong ⟩ sym (inverseʳ y) ⟩
    x ∙ (y ∙ y ⁻¹) ≈⟨ sym (assoc x y (y ⁻¹)) ⟩
    (x ∙ y) ∙ y ⁻¹ ∎

  right-helper : ∀ x y → y ≈ x ⁻¹ ∙ (x ∙ y)
  right-helper x y = begin
    y              ≈⟨ sym (identityˡ y) ⟩
    ε          ∙ y ≈⟨ sym (inverseˡ x) ⟨ ∙-cong ⟩ refl ⟩
    (x ⁻¹ ∙ x) ∙ y ≈⟨ assoc (x ⁻¹) x y ⟩
    x ⁻¹ ∙ (x ∙ y) ∎

left-identity-unique : ∀ x y → x ∙ y ≈ y → x ≈ ε
left-identity-unique x y eq = begin
  x              ≈⟨ left-helper x y ⟩
  (x ∙ y) ∙ y ⁻¹ ≈⟨ eq ⟨ ∙-cong ⟩ refl ⟩
       y  ∙ y ⁻¹ ≈⟨ inverseʳ y ⟩
  ε              ∎

right-identity-unique : ∀ x y → x ∙ y ≈ x → y ≈ ε
right-identity-unique x y eq = begin
  y              ≈⟨ right-helper x y ⟩
  x ⁻¹ ∙ (x ∙ y) ≈⟨ refl ⟨ ∙-cong ⟩ eq ⟩
  x ⁻¹ ∙  x      ≈⟨ inverseˡ x ⟩
  ε              ∎

identity-unique : ∀ {x} → Identity x _∙_ → x ≈ ε
identity-unique {x} id = left-identity-unique x x (proj₂ id x)

left-inverse-unique : ∀ x y → x ∙ y ≈ ε → x ≈ y ⁻¹
left-inverse-unique x y eq = begin
  x              ≈⟨ left-helper x y ⟩
  (x ∙ y) ∙ y ⁻¹ ≈⟨ eq ⟨ ∙-cong ⟩ refl ⟩
       ε  ∙ y ⁻¹ ≈⟨ identityˡ (y ⁻¹) ⟩
            y ⁻¹ ∎

right-inverse-unique : ∀ x y → x ∙ y ≈ ε → y ≈ x ⁻¹
right-inverse-unique x y eq = begin
  y       ≈⟨ sym (⁻¹-involutive y) ⟩
  y ⁻¹ ⁻¹ ≈⟨ ⁻¹-cong (sym (left-inverse-unique x y eq)) ⟩
  x ⁻¹    ∎
