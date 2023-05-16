------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra using (MoufangLoop)

module Algebra.Properties.MoufangLoop {a ℓ} (M : MoufangLoop a ℓ) where

open MoufangLoop M
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid setoid
open import Data.Product

alternativeˡ : LeftAlternative _∙_
alternativeˡ x y = begin
  (x ∙ x) ∙ y       ≈⟨ ∙-congʳ (∙-congˡ (sym (identityˡ x))) ⟩
  (x ∙ (ε ∙ x)) ∙ y ≈⟨ sym (leftBol x ε y) ⟩
  x ∙ (ε ∙ (x ∙ y)) ≈⟨ ∙-congˡ (identityˡ ((x ∙ y))) ⟩
  x ∙ (x ∙ y)       ∎

alternativeʳ : RightAlternative _∙_
alternativeʳ x y = begin
  x ∙ (y ∙ y)         ≈⟨ ∙-congˡ(∙-congʳ(sym (identityʳ y))) ⟩
  x ∙ ((y ∙ ε) ∙ y)   ≈⟨ sym (rightBol y ε x) ⟩
  ((x ∙ y) ∙ ε ) ∙ y  ≈⟨ ∙-congʳ (identityʳ ((x ∙ y))) ⟩
  (x ∙ y) ∙ y         ∎

alternative : Alternative _∙_
alternative = alternativeˡ , alternativeʳ

flex : Flexible _∙_
flex x y = begin
  (x ∙ y) ∙ x       ≈⟨ ∙-congˡ (sym (identityˡ x)) ⟩
  (x ∙ y) ∙ (ε ∙ x) ≈⟨ identical y ε x ⟩
  x ∙ ((y ∙ ε) ∙ x) ≈⟨ ∙-congˡ (∙-congʳ (identityʳ y)) ⟩
  x ∙ (y ∙ x)       ∎

z∙xzy≈zxz∙y : ∀ x y z → (z ∙ (x ∙ (z ∙ y))) ≈ (((z ∙ x) ∙ z) ∙ y)
z∙xzy≈zxz∙y x y z = sym (begin
  ((z ∙ x) ∙ z) ∙ y ≈⟨ (∙-congʳ (flex z x )) ⟩
  (z ∙ (x ∙ z)) ∙ y ≈⟨ sym (leftBol z x y) ⟩
  z ∙ (x ∙ (z ∙ y)) ∎)

x∙zyz≈xzy∙z : ∀ x y z → (x ∙ (z ∙ (y ∙ z))) ≈ (((x ∙ z) ∙ y) ∙ z)
x∙zyz≈xzy∙z x y z = begin
  x ∙ (z ∙ (y ∙ z))  ≈⟨ (∙-congˡ (sym (flex z y ))) ⟩
  x ∙ ((z ∙ y) ∙  z) ≈⟨ sym (rightBol z y x) ⟩
  ((x ∙ z) ∙ y) ∙ z  ∎

z∙xyz≈zxy∙z : ∀ x y z → (z ∙ ((x ∙ y) ∙ z)) ≈ ((z ∙ (x ∙ y)) ∙ z)
z∙xyz≈zxy∙z x y z = sym (flex z (x ∙ y))
