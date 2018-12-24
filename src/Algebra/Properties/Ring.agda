------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.Ring {r₁ r₂} (R : Ring r₁ r₂) where

import Algebra.Properties.AbelianGroup as AGP
open import Function
import Relation.Binary.Reasoning.Equational as EqR

open Ring R
open EqR setoid

open AGP +-abelianGroup public
  renaming ( ⁻¹-involutive to -‿involutive
           ; left-identity-unique to +-left-identity-unique
           ; right-identity-unique to +-right-identity-unique
           ; identity-unique to +-identity-unique
           ; left-inverse-unique to +-left-inverse-unique
           ; right-inverse-unique to +-right-inverse-unique
           ; ⁻¹-∙-comm to -‿+-comm
           )

-‿*-distribˡ : ∀ x y → - x * y ≈ - (x * y)
-‿*-distribˡ x y = begin
  - x * y                        ≈⟨ sym $ +-identityʳ _ ⟩
  - x * y + 0#                   ≈⟨ +-congʳ $ sym (-‿inverseʳ _) ⟩
  - x * y + (x * y + - (x * y))  ≈⟨ sym $ +-assoc _ _ _  ⟩
  - x * y + x * y + - (x * y)    ≈⟨ +-congˡ $ sym (distribʳ _ _ _) ⟩
  (- x + x) * y + - (x * y)      ≈⟨ +-congˡ $ *-congˡ $ -‿inverseˡ _ ⟩
  0# * y + - (x * y)             ≈⟨ +-congˡ $ zeroˡ _ ⟩
  0# + - (x * y)                 ≈⟨ +-identityˡ _ ⟩
  - (x * y)                      ∎

-‿*-distribʳ : ∀ x y → x * - y ≈ - (x * y)
-‿*-distribʳ x y = begin
  x * - y                        ≈⟨ sym $ +-identityˡ _ ⟩
  0# + x * - y                   ≈⟨ +-congˡ $ sym (-‿inverseˡ _) ⟩
  - (x * y) + x * y + x * - y    ≈⟨ +-assoc _ _ _  ⟩
  - (x * y) + (x * y + x * - y)  ≈⟨ +-congʳ $ sym (distribˡ _ _ _)  ⟩
  - (x * y) + x * (y + - y)      ≈⟨ +-congʳ $ *-congʳ $ -‿inverseʳ _ ⟩
  - (x * y) + x * 0#             ≈⟨ +-congʳ $ zeroʳ _ ⟩
  - (x * y) + 0#                 ≈⟨ +-identityʳ _ ⟩
  - (x * y)                      ∎
