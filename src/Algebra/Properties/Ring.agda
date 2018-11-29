------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Algebra

module Algebra.Properties.Ring {r₁ r₂} (R : Ring r₁ r₂) where

import Algebra.Properties.AbelianGroup as AGP
open import Function
import Relation.Binary.EqReasoning as EqR

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
  - x * y + 0#                   ≈⟨ refl ⟨ +-cong ⟩ sym (-‿inverseʳ _) ⟩
  - x * y + (x * y + - (x * y))  ≈⟨ sym $ +-assoc _ _ _  ⟩
  - x * y + x * y + - (x * y)    ≈⟨ sym (distribʳ _ _ _) ⟨ +-cong ⟩ refl ⟩
  (- x + x) * y + - (x * y)      ≈⟨ (-‿inverseˡ _ ⟨ *-cong ⟩ refl)
                                      ⟨ +-cong ⟩
                                    refl ⟩
  0# * y + - (x * y)             ≈⟨ zeroˡ _ ⟨ +-cong ⟩ refl ⟩
  0# + - (x * y)                 ≈⟨ +-identityˡ _ ⟩
  - (x * y)                      ∎

-‿*-distribʳ : ∀ x y → x * - y ≈ - (x * y)
-‿*-distribʳ x y = begin
  x * - y                        ≈⟨ sym $ +-identityˡ _ ⟩
  0# + x * - y                   ≈⟨ sym (-‿inverseˡ _) ⟨ +-cong ⟩ refl ⟩
  - (x * y) + x * y + x * - y    ≈⟨ +-assoc _ _ _  ⟩
  - (x * y) + (x * y + x * - y)  ≈⟨ refl ⟨ +-cong ⟩ sym (distribˡ _ _ _)  ⟩
  - (x * y) + x * (y + - y)      ≈⟨ refl ⟨ +-cong ⟩ (refl ⟨ *-cong ⟩ -‿inverseʳ _) ⟩
  - (x * y) + x * 0#             ≈⟨ refl ⟨ +-cong ⟩ zeroʳ _ ⟩
  - (x * y) + 0#                 ≈⟨ +-identityʳ _ ⟩
  - (x * y)                      ∎
