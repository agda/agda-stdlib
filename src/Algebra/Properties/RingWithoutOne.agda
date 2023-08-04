------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of RingWithoutOne
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra

module Algebra.Properties.RingWithoutOne {r₁ r₂} (R : RingWithoutOne r₁ r₂) where

open RingWithoutOne R

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

-‿distribˡ-* : ∀ x y → - (x * y) ≈ - x * y
-‿distribˡ-* x y = sym $ begin
  - x * y                        ≈⟨ sym $ +-identityʳ (- x * y) ⟩
  - x * y + 0#                   ≈⟨ +-congˡ $ sym ( -‿inverseʳ (x * y) ) ⟩
  - x * y + (x * y + - (x * y))  ≈⟨ sym $ +-assoc (- x * y) (x * y) (- (x * y))  ⟩
  - x * y + x * y + - (x * y)    ≈⟨ +-congʳ $ sym ( distribʳ y (- x) x ) ⟩
  (- x + x) * y + - (x * y)      ≈⟨ +-congʳ $ *-congʳ $ -‿inverseˡ x ⟩
  0# * y + - (x * y)             ≈⟨ +-congʳ $ zeroˡ y ⟩
  0# + - (x * y)                 ≈⟨ +-identityˡ (- (x * y)) ⟩
  - (x * y)                      ∎

-‿distribʳ-* : ∀ x y → - (x * y) ≈ x * - y
-‿distribʳ-* x y = sym $ begin
  x * - y                        ≈⟨ sym $ +-identityˡ (x * (- y)) ⟩
  0# + x * - y                   ≈⟨ +-congʳ $ sym ( -‿inverseˡ (x * y) ) ⟩
  - (x * y) + x * y + x * - y    ≈⟨ +-assoc (- (x * y)) (x * y) (x * (- y)) ⟩
  - (x * y) + (x * y + x * - y)  ≈⟨ +-congˡ $ sym ( distribˡ x y ( - y) )  ⟩
  - (x * y) + x * (y + - y)      ≈⟨ +-congˡ $ *-congˡ $ -‿inverseʳ y ⟩
  - (x * y) + x * 0#             ≈⟨ +-congˡ $ zeroʳ x ⟩
  - (x * y) + 0#                 ≈⟨ +-identityʳ (- (x * y)) ⟩
  - (x * y)                      ∎
