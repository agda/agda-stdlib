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
open import Function using (_$_)
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Export properties of abelian groups

open AbelianGroupProperties +-abelianGroup public
  renaming
  ( ε⁻¹≈ε            to -0#≈0#
  ; ∙-cancelˡ        to +-cancelˡ
  ; ∙-cancelʳ        to +-cancelʳ
  ; ∙-cancel         to +-cancel
  ; ⁻¹-involutive    to -‿involutive
  ; identityˡ-unique to +-identityˡ-unique
  ; identityʳ-unique to +-identityʳ-unique
  ; identity-unique  to +-identity-unique
  ; inverseˡ-unique  to +-inverseˡ-unique
  ; inverseʳ-unique  to +-inverseʳ-unique
  ; ⁻¹-∙-comm        to -‿+-comm
  -- DEPRECATED
  ; left-identity-unique  to +-left-identity-unique
  ; right-identity-unique to +-right-identity-unique
  ; left-inverse-unique   to +-left-inverse-unique
  ; right-inverse-unique  to +-right-inverse-unique
  )

------------------------------------------------------------------------
-- Ring properties

-‿distribˡ-* : ∀ x y → - (x * y) ≈ - x * y
-‿distribˡ-* x y = sym $ begin
  - x * y                        ≈⟨ sym $ +-identityʳ _ ⟩
  - x * y + 0#                   ≈⟨ +-congˡ $ sym (-‿inverseʳ _) ⟩
  - x * y + (x * y + - (x * y))  ≈⟨ sym $ +-assoc _ _ _  ⟩
  - x * y + x * y + - (x * y)    ≈⟨ +-congʳ $ sym (distribʳ _ _ _) ⟩
  (- x + x) * y + - (x * y)      ≈⟨ +-congʳ $ *-congʳ $ -‿inverseˡ _ ⟩
  0# * y + - (x * y)             ≈⟨ +-congʳ $ zeroˡ _ ⟩
  0# + - (x * y)                 ≈⟨ +-identityˡ _ ⟩
  - (x * y)                      ∎

-‿distribʳ-* : ∀ x y → - (x * y) ≈ x * - y
-‿distribʳ-* x y = sym $ begin
  x * - y                        ≈⟨ sym $ +-identityˡ _ ⟩
  0# + x * - y                   ≈⟨ +-congʳ $ sym (-‿inverseˡ _) ⟩
  - (x * y) + x * y + x * - y    ≈⟨ +-assoc _ _ _  ⟩
  - (x * y) + (x * y + x * - y)  ≈⟨ +-congˡ $ sym (distribˡ _ _ _)  ⟩
  - (x * y) + x * (y + - y)      ≈⟨ +-congˡ $ *-congˡ $ -‿inverseʳ _ ⟩
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
-‿*-distribˡ x y = sym (-‿distribˡ-* x y)
{-# WARNING_ON_USAGE -‿*-distribˡ
"Warning: -‿*-distribˡ was deprecated in v1.1.
Please use -‿distribˡ-* instead.
NOTE: the equality is flipped so you will need sym (-‿distribˡ-* ...)."
#-}
-‿*-distribʳ : ∀ x y → x * - y ≈ - (x * y)
-‿*-distribʳ x y = sym (-‿distribʳ-* x y)
{-# WARNING_ON_USAGE -‿*-distribʳ
"Warning: -‿*-distribʳ was deprecated in v1.1.
Please use -‿distribʳ-* instead.
NOTE: the equality is flipped so you will need sym (-‿distribʳ-* ...)."
#-}
