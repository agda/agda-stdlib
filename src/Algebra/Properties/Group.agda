------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.Group {g₁ g₂} (G : Group g₁ g₂) where

open Group G
open import Algebra.FunctionProperties _≈_
open import Relation.Binary.Reasoning.Setoid setoid
open import Function
open import Data.Product

ε⁻¹≈ε : ε ⁻¹ ≈ ε
ε⁻¹≈ε = begin
  ε ⁻¹      ≈⟨ sym $ identityʳ (ε ⁻¹) ⟩
  ε ⁻¹ ∙ ε  ≈⟨ inverseˡ ε ⟩
  ε         ∎

∙-cancelˡ : LeftCancellative _∙_
∙-cancelˡ x {y} {z} eq = begin
  y               ≈⟨ sym $ identityˡ y ⟩
  ε ∙ y           ≈⟨ sym $ ∙-congʳ $ inverseˡ x ⟩
  (x ⁻¹ ∙ x) ∙ y  ≈⟨ assoc (x ⁻¹) x y ⟩
  x ⁻¹ ∙ (x ∙ y)  ≈⟨ ∙-congˡ eq ⟩
  x ⁻¹ ∙ (x ∙ z)  ≈⟨ sym $ assoc (x ⁻¹) x z ⟩
  (x ⁻¹ ∙ x) ∙ z  ≈⟨ ∙-congʳ $ inverseˡ x ⟩
  ε ∙ z           ≈⟨ identityˡ z ⟩
  z               ∎

∙-cancelʳ : RightCancellative _∙_
∙-cancelʳ {x} y z eq = begin
  y               ≈⟨ sym $ identityʳ y ⟩
  y ∙ ε           ≈⟨ sym $ ∙-congˡ $ inverseʳ x ⟩
  y ∙ (x ∙ x ⁻¹)  ≈⟨ sym $ assoc y x (x ⁻¹) ⟩
  (y ∙ x) ∙ x ⁻¹  ≈⟨ ∙-congʳ eq ⟩
  (z ∙ x) ∙ x ⁻¹  ≈⟨ assoc z x (x ⁻¹) ⟩
  z ∙ (x ∙ x ⁻¹)  ≈⟨ ∙-congˡ $ inverseʳ x ⟩
  z ∙ ε           ≈⟨ identityʳ z ⟩
  z               ∎

∙-cancel : Cancellative _∙_
∙-cancel = ∙-cancelˡ , ∙-cancelʳ

⁻¹-involutive : ∀ x → x ⁻¹ ⁻¹ ≈ x
⁻¹-involutive x = begin
  x ⁻¹ ⁻¹               ≈⟨ sym $ identityʳ _ ⟩
  x ⁻¹ ⁻¹ ∙ ε           ≈⟨ ∙-congˡ $ sym (inverseˡ _) ⟩
  x ⁻¹ ⁻¹ ∙ (x ⁻¹ ∙ x)  ≈⟨ sym $ assoc _ _ _ ⟩
  x ⁻¹ ⁻¹ ∙ x ⁻¹ ∙ x    ≈⟨ ∙-congʳ $ inverseˡ _ ⟩
  ε ∙ x                 ≈⟨ identityˡ _ ⟩
  x                     ∎

private

  left-helper : ∀ x y → x ≈ (x ∙ y) ∙ y ⁻¹
  left-helper x y = begin
    x              ≈⟨ sym (identityʳ x) ⟩
    x ∙ ε          ≈⟨ ∙-congˡ $ sym (inverseʳ y) ⟩
    x ∙ (y ∙ y ⁻¹) ≈⟨ sym (assoc x y (y ⁻¹)) ⟩
    (x ∙ y) ∙ y ⁻¹ ∎

  right-helper : ∀ x y → y ≈ x ⁻¹ ∙ (x ∙ y)
  right-helper x y = begin
    y              ≈⟨ sym (identityˡ y) ⟩
    ε          ∙ y ≈⟨ ∙-congʳ $ sym (inverseˡ x) ⟩
    (x ⁻¹ ∙ x) ∙ y ≈⟨ assoc (x ⁻¹) x y ⟩
    x ⁻¹ ∙ (x ∙ y) ∎

identityˡ-unique : ∀ x y → x ∙ y ≈ y → x ≈ ε
identityˡ-unique x y eq = begin
  x              ≈⟨ left-helper x y ⟩
  (x ∙ y) ∙ y ⁻¹ ≈⟨ ∙-congʳ eq ⟩
       y  ∙ y ⁻¹ ≈⟨ inverseʳ y ⟩
  ε              ∎

identityʳ-unique : ∀ x y → x ∙ y ≈ x → y ≈ ε
identityʳ-unique x y eq = begin
  y              ≈⟨ right-helper x y ⟩
  x ⁻¹ ∙ (x ∙ y) ≈⟨ refl ⟨ ∙-cong ⟩ eq ⟩
  x ⁻¹ ∙  x      ≈⟨ inverseˡ x ⟩
  ε              ∎

identity-unique : ∀ {x} → Identity x _∙_ → x ≈ ε
identity-unique {x} id = identityˡ-unique x x (proj₂ id x)

inverseˡ-unique : ∀ x y → x ∙ y ≈ ε → x ≈ y ⁻¹
inverseˡ-unique x y eq = begin
  x              ≈⟨ left-helper x y ⟩
  (x ∙ y) ∙ y ⁻¹ ≈⟨ ∙-congʳ eq ⟩
       ε  ∙ y ⁻¹ ≈⟨ identityˡ (y ⁻¹) ⟩
            y ⁻¹ ∎

inverseʳ-unique : ∀ x y → x ∙ y ≈ ε → y ≈ x ⁻¹
inverseʳ-unique x y eq = begin
  y       ≈⟨ sym (⁻¹-involutive y) ⟩
  y ⁻¹ ⁻¹ ≈⟨ ⁻¹-cong (sym (inverseˡ-unique x y eq)) ⟩
  x ⁻¹    ∎


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

left-identity-unique = identityˡ-unique
{-# WARNING_ON_USAGE left-identity-unique
"Warning: left-identity-unique was deprecated in v1.1.
Please use identityˡ-unique instead."
#-}
right-identity-unique = identityʳ-unique
{-# WARNING_ON_USAGE right-identity-unique
"Warning: right-identity-unique was deprecated in v1.1.
Please use identityʳ-unique instead."
#-}
left-inverse-unique = inverseˡ-unique
{-# WARNING_ON_USAGE left-inverse-unique
"Warning: left-inverse-unique was deprecated in v1.1.
Please use inverseˡ-unique instead."
#-}
right-inverse-unique = inverseʳ-unique
{-# WARNING_ON_USAGE right-inverse-unique
"Warning: right-inverse-unique was deprecated in v1.1.
Please use inverseʳ-unique instead."
#-}
