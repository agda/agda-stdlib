------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Rings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Ring)

module Algebra.Properties.Ring {r₁ r₂} (R : Ring r₁ r₂) where

open Ring R

import Algebra.Properties.AbelianGroup as AbelianGroupProperties
open import Function.Base using (_$_)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Definitions _≈_
open import Data.Product

------------------------------------------------------------------------
-- Export properties of abelian groups

open AbelianGroupProperties +-abelianGroup public
  renaming
  ( ε⁻¹≈ε            to -0#≈0#
  ; ∙-cancelˡ        to +-cancelˡ
  ; ∙-cancelʳ        to +-cancelʳ
  ; ∙-cancel         to +-cancel
  ; ⁻¹-involutive    to -‿involutive
  ; ⁻¹-injective     to -‿injective
  ; ⁻¹-anti-homo-∙   to -‿anti-homo-+
  ; identityˡ-unique to +-identityˡ-unique
  ; identityʳ-unique to +-identityʳ-unique
  ; identity-unique  to +-identity-unique
  ; inverseˡ-unique  to +-inverseˡ-unique
  ; inverseʳ-unique  to +-inverseʳ-unique
  ; ⁻¹-∙-comm        to -‿+-comm
  )

------------------------------------------------------------------------
-- Properties of -_

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

-1*x≈-x : ∀ x → - 1# * x ≈ - x
-1*x≈-x x = begin
  - 1# * x    ≈⟨ sym (-‿distribˡ-* 1# x ) ⟩
  - (1# * x)  ≈⟨ -‿cong ( *-identityˡ x ) ⟩
  - x         ∎

zeroʳ-unique : ∀ x z → x + z ≈ x → z ≈ 0#
zeroʳ-unique x z eq = begin
  z              ≈⟨ sym (+-identityˡ z) ⟩
  0# + z         ≈⟨ +-congʳ (sym (-‿inverseʳ x)) ⟩
  x - x + z      ≈⟨ +-congʳ (+-comm x (- x)) ⟩
  - x + x + z    ≈⟨ +-assoc (- x) x z ⟩
  - x + (x + z)  ≈⟨ +-congˡ eq ⟩
  - x + x        ≈⟨ -‿inverseˡ x ⟩
  0#             ∎

zeroˡ-unique : ∀ x z → z + x ≈ x → z ≈ 0#
zeroˡ-unique x z eq = begin
  z            ≈⟨ sym (+-identityʳ z) ⟩
  z + 0#       ≈⟨ +-congˡ (sym (-‿inverseʳ x)) ⟩
  z + (x - x)  ≈⟨ sym(+-assoc z x (- x)) ⟩
  z + x - x    ≈⟨ +-congʳ eq ⟩
  x - x        ≈⟨ -‿inverseʳ x ⟩
  0#           ∎

zero-unique : ∀ z → Zero z _+_ → z ≈ 0#
zero-unique z x = zeroˡ-unique z z (proj₂ x z)

x≈0 : ∀ x → x + x ≈ x → x ≈ 0#
x≈0 x eq = begin
  x            ≈⟨ sym(+-identityʳ x) ⟩
  x + 0#       ≈⟨ +-congˡ (sym (-‿inverseʳ x)) ⟩
  x + (x - x)  ≈⟨ sym (+-assoc x x (- x)) ⟩
  x + x - x    ≈⟨ +-congʳ(eq) ⟩
  x - x        ≈⟨ -‿inverseʳ x ⟩
  0#           ∎

xy-z≈xy-xz : ∀ x y z → x * (y - z) ≈ x * y - x * z
xy-z≈xy-xz x y z = begin
  x * (y - z)      ≈⟨ distribˡ x y (- z) ⟩
  x * y + x * - z  ≈⟨ +-congˡ (sym (-‿distribʳ-* x z)) ⟩
  x * y - x * z    ∎

y-zx≈yx-zx : ∀ x y z → (y - z) * x ≈ (y * x) - (z * x)
y-zx≈yx-zx x y z = begin
  (y - z) * x      ≈⟨ distribʳ x y (- z) ⟩
  y * x + - z * x  ≈⟨ +-congˡ (sym (-‿distribˡ-* z x)) ⟩
  y * x - z * x    ∎
