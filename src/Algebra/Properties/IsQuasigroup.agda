------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Quasigroups
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Structures.IsQuasigroup using (IsQuasigroup)

module Algebra.Properties.IsQuasigroup
  {a ℓ} {A} {_≈_} {_∙_ _\\_ _//_}
  (isQuasigroup : IsQuasigroup {a = a} {ℓ} {A = A}_≈_ _∙_ _\\_ _//_) where

open import Algebra.Definitions _≈_
open import Data.Product.Base using (_,_)

open IsQuasigroup isQuasigroup
open import Relation.Binary.Reasoning.Setoid setoid

cancelˡ : LeftCancellative _∙_
cancelˡ x y z eq = begin
  y             ≈⟨ leftDividesʳ x y ⟨
  x \\ (x ∙ y)  ≈⟨ \\-congˡ eq ⟩
  x \\ (x ∙ z)  ≈⟨ leftDividesʳ x z ⟩
  z             ∎

cancelʳ : RightCancellative _∙_
cancelʳ x y z eq = begin
  y             ≈⟨ rightDividesʳ x y ⟨
  (y ∙ x) // x  ≈⟨ //-congʳ eq ⟩
  (z ∙ x) // x  ≈⟨ rightDividesʳ x z ⟩
  z             ∎

cancel : Cancellative _∙_
cancel = cancelˡ , cancelʳ

y≈x\\z : ∀ x y z → (x ∙ y) ≈ z → y ≈ (x \\ z)
y≈x\\z x y z eq = begin
  y            ≈⟨ leftDividesʳ x y ⟨
  x \\ (x ∙ y) ≈⟨ \\-congˡ eq ⟩
  x \\ z       ∎

x≈z//y : ∀ x y z → (x ∙ y) ≈ z → x ≈ (z // y)
x≈z//y x y z eq = begin
  x            ≈⟨ rightDividesʳ y x ⟨
  (x ∙ y) // y ≈⟨ //-congʳ eq ⟩
  z // y       ∎
