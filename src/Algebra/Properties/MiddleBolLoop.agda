------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Quasigroup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (MiddleBolLoop)

module Algebra.Properties.MiddleBolLoop {m₁ m₂} (M : MiddleBolLoop m₁ m₂) where

open MiddleBolLoop M
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid setoid
open import Data.Product

x/x≈ε : ∀ x → x // x ≈ ε
x/x≈ε x = begin
  x // x ≈⟨ //-congʳ (sym (identityˡ x)) ⟩
  (ε ∙ x) // x ≈⟨ rightDividesʳ x ε ⟩
  ε ∎

x\x≈ε : ∀ x → x \\ x ≈ ε
x\x≈ε x = begin
  x \\ x ≈⟨ \\-congˡ (sym (identityʳ x )) ⟩
  x \\ (x ∙ ε) ≈⟨ leftDividesʳ x ε ⟩
  ε ∎

ε\x≈x : ∀ x → ε \\ x ≈ x
ε\x≈x x = begin
  ε \\ x ≈⟨ sym (identityˡ ((ε \\ x))) ⟩
  ε ∙ (ε \\ x) ≈⟨ leftDividesˡ ε x ⟩
  x ∎

y≈xz : ∀ x y z → x ∙ y ≈ z → y ≈ x \\ z
y≈xz x y z eq = begin
  y ≈⟨ sym (leftDividesʳ x y) ⟩
  x \\ (x ∙ y) ≈⟨ \\-congˡ eq ⟩
  x \\ z ∎

xyx\x≈y\x : ∀ x y → x ∙ ((y ∙ x) \\ x) ≈ y \\ x
xyx\x≈y\x x y = begin
  x ∙ ((y ∙ x) \\ x)  ≈⟨ middleBol x y x ⟩
  (x // x) ∙ (y \\ x) ≈⟨ ∙-congʳ (x/x≈ε x) ⟩
  ε ∙ (y \\ x) ≈⟨ identityˡ ((y \\ x)) ⟩
  y \\ x ∎

xxz\x≈x/z : ∀ x z → x ∙ ((x ∙ z) \\ x) ≈ x // z
xxz\x≈x/z x z = begin
  x ∙ ((x ∙ z) \\ x) ≈⟨ middleBol x x z ⟩
  (x // z) ∙ (x \\ x) ≈⟨ ∙-congˡ (x\x≈ε x) ⟩
  (x // z) ∙ ε ≈⟨ identityʳ ((x // z)) ⟩
  x // z ∎

xz\z≈x/zx : ∀ x z → x ∙ (z \\ x) ≈ (x // z) ∙ x
xz\z≈x/zx x z = begin
  x ∙ (z \\ x) ≈⟨ ∙-congˡ (\\-congʳ( sym (identityˡ z))) ⟩
  x ∙ ((ε ∙ z) \\ x) ≈⟨ middleBol x ε z ⟩
  x // z ∙ (ε \\ x) ≈⟨ ∙-congˡ (ε\x≈x x) ⟩
  x // z ∙ x ∎
