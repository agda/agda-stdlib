------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Loop
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Loop)

module Algebra.Properties.Loop {l₁ l₂} (L : Loop l₁ l₂) where

open Loop L
open import Algebra.Definitions _≈_
open import Algebra.Properties.Quasigroup
open import Data.Product.Base using (proj₂)
open import Relation.Binary.Reasoning.Setoid setoid

x//x≈ε : ∀ x → x // x ≈ ε
x//x≈ε x = begin
  x // x       ≈⟨ //-congʳ (sym (identityˡ x)) ⟩
  (ε ∙ x) // x ≈⟨ rightDividesʳ x ε ⟩
  ε            ∎

x\\x≈ε : ∀ x → x \\ x ≈ ε
x\\x≈ε x = begin
  x \\ x       ≈⟨ \\-congˡ (sym (identityʳ x )) ⟩
  x \\ (x ∙ ε) ≈⟨ leftDividesʳ x ε ⟩
  ε            ∎

ε\\x≈x : ∀ x → ε \\ x ≈ x
ε\\x≈x x = begin
  ε \\ x       ≈⟨ sym (identityˡ (ε \\ x)) ⟩
  ε ∙ (ε \\ x) ≈⟨ leftDividesˡ ε x ⟩
  x            ∎

x//ε≈x : ∀ x → x // ε ≈ x
x//ε≈x x = begin
 x // ε       ≈⟨ sym (identityʳ (x // ε)) ⟩
 (x // ε) ∙ ε ≈⟨ rightDividesˡ ε x ⟩
 x            ∎

identityˡ-unique : ∀ x y → x ∙ y ≈ y → x ≈ ε
identityˡ-unique x y eq = begin
  x            ≈⟨ rightDividesʳ y x ⟨
  (x ∙ y) // y ≈⟨ //-congʳ eq ⟩
       y  // y ≈⟨ x//x≈ε y ⟩
  ε            ∎

identityʳ-unique : ∀ x y → x ∙ y ≈ x → y ≈ ε
identityʳ-unique x y eq = begin
  y            ≈⟨ leftDividesʳ x y ⟨
  x \\ (x ∙ y) ≈⟨ \\-congˡ  eq ⟩
  x \\ x       ≈⟨ x\\x≈ε x ⟩
  ε            ∎

identity-unique : ∀ {x} → Identity x _∙_ → x ≈ ε
identity-unique {x} id = identityˡ-unique x x (proj₂ id x)

