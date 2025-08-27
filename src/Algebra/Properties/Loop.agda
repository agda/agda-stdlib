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
open import Algebra.Properties.Quasigroup quasigroup
open import Data.Product.Base using (proj₂)
open import Relation.Binary.Reasoning.Setoid setoid

x//x≈ε : ∀ x → x // x ≈ ε
x//x≈ε x = sym (x≈z//y _ _ _ (identityˡ x))

x\\x≈ε : ∀ x → x \\ x ≈ ε
x\\x≈ε x = sym (y≈x\\z _ _ _ (identityʳ x))

ε\\x≈x : ∀ x → ε \\ x ≈ x
ε\\x≈x x = sym (y≈x\\z _ _ _ (identityˡ x))

x//ε≈x : ∀ x → x // ε ≈ x
x//ε≈x x = sym (x≈z//y _ _ _ (identityʳ x))

identityˡ-unique : ∀ x y → x ∙ y ≈ y → x ≈ ε
identityˡ-unique x y eq = begin
  x      ≈⟨ x≈z//y x y y eq ⟩
  y // y ≈⟨ x//x≈ε y ⟩
  ε      ∎

identityʳ-unique : ∀ x y → x ∙ y ≈ x → y ≈ ε
identityʳ-unique x y eq = begin
  y       ≈⟨ y≈x\\z x y x eq ⟩
  x \\ x  ≈⟨ x\\x≈ε x ⟩
  ε       ∎

identity-unique : ∀ {x} → Identity x _∙_ → x ≈ ε
identity-unique {x} id = identityˡ-unique x x (proj₂ id x)

