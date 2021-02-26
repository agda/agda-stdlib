------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Rings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.Ring {r₁ r₂} (R : Ring r₁ r₂) where

open Ring R

import Algebra.Properties.AbelianGroup as AbelianGroupProperties
open import Function.Base using (_$_)
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Export properties of abelian groups

open AbelianGroupProperties +-abelianGroup public
  renaming
  ( ε⁻¹≈ε            to -0#≈0#
  ; ∙-cancelˡ        to +-cancelˡ
  ; ∙-cancelʳ        to +-cancelʳ
  ; ∙-cancel         to +-cancel
  ; ⁻¹-involutive    to neg-involutive
  ; ⁻¹-injective     to neg-injective
  ; ⁻¹-anti-homo-∙   to neg-anti-homo-+
  ; identityˡ-unique to +-identityˡ-unique
  ; identityʳ-unique to +-identityʳ-unique
  ; identity-unique  to +-identity-unique
  ; inverseˡ-unique  to +-inverseˡ-unique
  ; inverseʳ-unique  to +-inverseʳ-unique
  ; ⁻¹-distrib-∙     to neg-distrib-+
  -- DEPRECATED
  ; left-identity-unique  to +-left-identity-unique
  ; right-identity-unique to +-right-identity-unique
  ; left-inverse-unique   to +-left-inverse-unique
  ; right-inverse-unique  to +-right-inverse-unique
  ; ⁻¹-∙-comm             to -‿+-comm
  )

------------------------------------------------------------------------
-- Properties of -_

neg-distribˡ-* : ∀ x y → - (x * y) ≈ - x * y
neg-distribˡ-* x y = sym $ begin
  - x * y                        ≈⟨ sym $ +-identityʳ _ ⟩
  - x * y + 0#                   ≈⟨ +-congˡ $ sym (+-inverseʳ _) ⟩
  - x * y + (x * y + - (x * y))  ≈⟨ sym $ +-assoc _ _ _  ⟩
  - x * y + x * y + - (x * y)    ≈⟨ +-congʳ $ sym (distribʳ _ _ _) ⟩
  (- x + x) * y + - (x * y)      ≈⟨ +-congʳ $ *-congʳ $ +-inverseˡ _ ⟩
  0# * y + - (x * y)             ≈⟨ +-congʳ $ zeroˡ _ ⟩
  0# + - (x * y)                 ≈⟨ +-identityˡ _ ⟩
  - (x * y)                      ∎

neg-distribʳ-* : ∀ x y → - (x * y) ≈ x * - y
neg-distribʳ-* x y = sym $ begin
  x * - y                        ≈⟨ sym $ +-identityˡ _ ⟩
  0# + x * - y                   ≈⟨ +-congʳ $ sym (+-inverseˡ _) ⟩
  - (x * y) + x * y + x * - y    ≈⟨ +-assoc _ _ _  ⟩
  - (x * y) + (x * y + x * - y)  ≈⟨ +-congˡ $ sym (distribˡ _ _ _)  ⟩
  - (x * y) + x * (y + - y)      ≈⟨ +-congˡ $ *-congˡ $ +-inverseʳ _ ⟩
  - (x * y) + x * 0#             ≈⟨ +-congˡ $ zeroʳ _ ⟩
  - (x * y) + 0#                 ≈⟨ +-identityʳ _ ⟩
  - (x * y)                      ∎


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

-‿*-distribˡ : ∀ x y → - x * y ≈ - (x * y)
-‿*-distribˡ x y = sym (neg-distribˡ-* x y)
{-# WARNING_ON_USAGE -‿*-distribˡ
"Warning: -‿*-distribˡ was deprecated in v1.1.
Please use neg-distribˡ-* instead.
NOTE: the equality is flipped so you will need sym (neg-distribˡ-* ...)."
#-}
-‿*-distribʳ : ∀ x y → x * - y ≈ - (x * y)
-‿*-distribʳ x y = sym (neg-distribʳ-* x y)
{-# WARNING_ON_USAGE -‿*-distribʳ
"Warning: -‿*-distribʳ was deprecated in v1.1.
Please use neg-distribʳ-* instead.
NOTE: the equality is flipped so you will need sym (neg-distribʳ-* ...)."
#-}

-- Version 1.6

-‿involutive = neg-involutive
{-# WARNING_ON_USAGE -‿involutive
"Warning: -‿involutive was deprecated in v1.6.
Please use neg-involutive instead."
#-}
-‿injective = neg-injective
{-# WARNING_ON_USAGE -‿injective
"Warning: -‿injective was deprecated in v1.6.
Please use neg-injective instead."
#-}
-‿anti-homo-+ = neg-anti-homo-+
{-# WARNING_ON_USAGE -‿anti-homo-+
"Warning: -‿anti-homo-+ was deprecated in v1.6.
Please use neg-anti-homo-+ instead."
#-}
-‿distribˡ-* = neg-distribˡ-*
{-# WARNING_ON_USAGE -‿distribˡ-*
"Warning: -‿distribˡ-* was deprecated in v1.6.
Please use neg-distribˡ-* instead."
#-}
-‿distribʳ-* = neg-distribʳ-*
{-# WARNING_ON_USAGE -‿distribʳ-*
"Warning: -‿distribʳ-* was deprecated in v1.6.
Please use neg-distribʳ-* instead."
#-}
