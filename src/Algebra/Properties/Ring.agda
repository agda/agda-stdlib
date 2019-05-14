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
import Relation.Binary.Reasoning.Setoid as EqR

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
  - x * y + 0#                   ≈⟨ +-congˡ $ sym (-‿inverseʳ _) ⟩
  - x * y + (x * y + - (x * y))  ≈⟨ sym $ +-assoc _ _ _  ⟩
  - x * y + x * y + - (x * y)    ≈⟨ +-congʳ $ sym (distribʳ _ _ _) ⟩
  (- x + x) * y + - (x * y)      ≈⟨ +-congʳ $ *-congʳ $ -‿inverseˡ _ ⟩
  0# * y + - (x * y)             ≈⟨ +-congʳ $ zeroˡ _ ⟩
  0# + - (x * y)                 ≈⟨ +-identityˡ _ ⟩
  - (x * y)                      ∎

-‿*-distribʳ : ∀ x y → x * - y ≈ - (x * y)
-‿*-distribʳ x y = begin
  x * - y                        ≈⟨ sym $ +-identityˡ _ ⟩
  0# + x * - y                   ≈⟨ +-congʳ $ sym (-‿inverseˡ _) ⟩
  - (x * y) + x * y + x * - y    ≈⟨ +-assoc _ _ _  ⟩
  - (x * y) + (x * y + x * - y)  ≈⟨ +-congˡ $ sym (distribˡ _ _ _)  ⟩
  - (x * y) + x * (y + - y)      ≈⟨ +-congˡ $ *-congˡ $ -‿inverseʳ _ ⟩
  - (x * y) + x * 0#             ≈⟨ +-congˡ $ zeroʳ _ ⟩
  - (x * y) + 0#                 ≈⟨ +-identityʳ _ ⟩
  - (x * y)                      ∎
