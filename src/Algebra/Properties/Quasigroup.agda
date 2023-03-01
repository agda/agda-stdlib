------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Quasigroup
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Quasigroup)

module Algebra.Properties.Quasigroup {q₁ q₂} (Q : Quasigroup q₁ q₂) where

open Quasigroup Q
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid setoid
open import Data.Product

cancelˡ : LeftCancellative _∙_
cancelˡ x y z eq = begin
  y             ≈⟨ sym( leftDividesʳ x y) ⟩
  x \\ (x ∙ y)  ≈⟨ \\-congˡ eq ⟩
  x \\ (x ∙ z)  ≈⟨ leftDividesʳ x z ⟩
  z             ∎

cancelʳ : RightCancellative _∙_
cancelʳ x y z eq = begin
  y             ≈⟨ sym( rightDividesʳ x y) ⟩
  (y ∙ x) // x  ≈⟨ //-congʳ eq ⟩
  (z ∙ x) // x  ≈⟨ rightDividesʳ x z ⟩
  z             ∎

cancel : Cancellative _∙_
cancel = cancelˡ , cancelʳ

y≈x\\z : ∀ x y z → x ∙ y ≈ z → y ≈ x \\ z
y≈x\\z x y z eq = begin
  y            ≈⟨ sym (leftDividesʳ x y) ⟩
  x \\ (x ∙ y) ≈⟨ \\-congˡ eq ⟩
  x \\ z       ∎

x≈z//y : ∀ x y z → x ∙ y ≈ z → x ≈ z // y
x≈z//y x y z eq = begin
  x            ≈⟨ sym (rightDividesʳ y x) ⟩
  (x ∙ y) // y ≈⟨ //-congʳ eq ⟩
  z // y       ∎
