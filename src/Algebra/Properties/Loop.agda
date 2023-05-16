------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Quasigroup
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Loop)

module Algebra.Properties.Loop {l₁ l₂} (L : Loop l₁ l₂) where

open Loop L
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid setoid
open import Data.Product
open import Algebra.Properties.Quasigroup

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
