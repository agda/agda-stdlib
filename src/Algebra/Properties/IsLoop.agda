------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Loops
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Structures.IsQuasigroup using (IsLoop)

module Algebra.Properties.IsLoop
  {a ℓ} {A} {_≈_} {_∙_ _\\_ _//_} {ε}
  (isLoop : IsLoop {a = a} {ℓ = ℓ} {A = A} _≈_ _∙_ _\\_ _//_ ε) where

open import Algebra.Definitions _≈_
open import Data.Product.Base using (proj₂)

open IsLoop isLoop
open import Algebra.Properties.IsQuasigroup isQuasigroup
open import Relation.Binary.Reasoning.Setoid setoid

x//x≈ε : ∀ x → (x // x) ≈ ε
x//x≈ε x = begin
  x // x       ≈⟨ //-congʳ (identityˡ x) ⟨
  (ε ∙ x) // x ≈⟨ rightDividesʳ x ε ⟩
  ε            ∎

x\\x≈ε : ∀ x → (x \\ x) ≈ ε
x\\x≈ε x = begin
  x \\ x       ≈⟨ \\-congˡ (identityʳ x ) ⟨
  x \\ (x ∙ ε) ≈⟨ leftDividesʳ x ε ⟩
  ε            ∎

ε\\x≈x : ∀ x → (ε \\ x) ≈ x
ε\\x≈x x = begin
  ε \\ x       ≈⟨ identityˡ (ε \\ x) ⟨
  ε ∙ (ε \\ x) ≈⟨ leftDividesˡ ε x ⟩
  x            ∎

x//ε≈x : ∀ x → (x // ε) ≈ x
x//ε≈x x = begin
 x // ε       ≈⟨ identityʳ (x // ε) ⟨
 (x // ε) ∙ ε ≈⟨ rightDividesˡ ε x ⟩
 x            ∎

identityˡ-unique : ∀ x y → (x ∙ y) ≈ y → x ≈ ε
identityˡ-unique x y eq = begin
  x      ≈⟨ x≈z//y x y y eq ⟩
  y // y ≈⟨ x//x≈ε y ⟩
  ε      ∎

identityʳ-unique : ∀ x y → (x ∙ y) ≈ x → y ≈ ε
identityʳ-unique x y eq = begin
  y       ≈⟨ y≈x\\z x y x eq ⟩
  x \\ x  ≈⟨ x\\x≈ε x ⟩
  ε       ∎

identity-unique : ∀ {x} → Identity x _∙_ → x ≈ ε
identity-unique {x} id = identityˡ-unique x x (proj₂ id x)

