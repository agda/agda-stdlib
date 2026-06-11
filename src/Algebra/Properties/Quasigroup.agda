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
open import Data.Product.Base using (_,_)

y≈x\\z : ∀ x y z → x ∙ y ≈ z → y ≈ x \\ z
y≈x\\z x y z eq = begin
  y            ≈⟨ leftDividesʳ x y ⟨
  x \\ (x ∙ y) ≈⟨ \\-congˡ eq ⟩
  x \\ z       ∎

x≈z//y : ∀ x y z → x ∙ y ≈ z → x ≈ z // y
x≈z//y x y z eq = begin
  x            ≈⟨ rightDividesʳ y x ⟨
  (x ∙ y) // y ≈⟨ //-congʳ eq ⟩
  z // y       ∎

cancelˡ : LeftCancellative _∙_
cancelˡ x y z eq = begin
  y             ≈⟨ y≈x\\z x y (x ∙ z) eq ⟩
  x \\ (x ∙ z)  ≈⟨ leftDividesʳ x z ⟩
  z             ∎

cancelʳ : RightCancellative _∙_
cancelʳ x y z eq = begin
  y             ≈⟨ x≈z//y y x (z ∙ x) eq ⟩
  (z ∙ x) // x  ≈⟨ rightDividesʳ x z ⟩
  z             ∎

cancel : Cancellative _∙_
cancel = cancelˡ , cancelʳ
