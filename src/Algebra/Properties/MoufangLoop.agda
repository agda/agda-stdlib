------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (MoufangLoop)

module Algebra.Properties.MoufangLoop {a ℓ} (M : MoufangLoop a ℓ) where

open MoufangLoop M
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid setoid
open import Data.Product

leftAlternative : LeftBol _∙_ → LeftAlternative _∙_
leftAlternative eq x y  = begin
  ((x ∙ x) ∙ y)         ≈⟨ ∙-congʳ (∙-congˡ (sym (identityˡ x))) ⟩
  ((x ∙ (ε ∙ x)) ∙ y)   ≈⟨ sym (eq x ε y) ⟩
  (x ∙ (ε ∙ (x ∙ y)))   ≈⟨ ∙-congˡ (identityˡ ((x ∙ y))) ⟩
  (x ∙ (x ∙ y))         ∎

rightAlternative : RightBol _∙_ → RightAlternative _∙_
rightAlternative eq x y = begin
  (x ∙ (y ∙ y))         ≈⟨ ∙-congˡ(∙-congʳ(sym (identityʳ y))) ⟩
  (x ∙ ((y ∙ ε) ∙ y))   ≈⟨ sym( eq y ε x ) ⟩
  (((x ∙ y) ∙ ε ) ∙ y)  ≈⟨ ∙-congʳ (identityʳ ((x ∙ y))) ⟩
  ((x ∙ y) ∙ y)         ∎

alternative : LeftBol _∙_ → RightBol _∙_ → Alternative _∙_
alternative x y = (leftAlternative x) , rightAlternative y

z∙xzy≈zxz∙y : ∀ x y z → (z ∙ (x ∙ (z ∙ y))) ≈ (((z ∙ x) ∙ z) ∙ y)
z∙xzy≈zxz∙y x y z = sym (begin
  (((z ∙ x) ∙ z) ∙ y) ≈⟨ (∙-congʳ (flex z x )) ⟩
  ((z ∙ (x ∙ z)) ∙ y) ≈⟨ sym (leftBol z x y) ⟩
  (z ∙ (x ∙ (z ∙ y))) ∎)

x∙zyz≈xzy∙z : ∀ x y z → (x ∙ (z ∙ (y ∙ z))) ≈ (((x ∙ z) ∙ y) ∙ z)
x∙zyz≈xzy∙z x y z = begin
  (x ∙ (z ∙ (y ∙ z)))  ≈⟨ (∙-congˡ (sym (flex z y ))) ⟩
  (x ∙ ((z ∙ y) ∙  z)) ≈⟨ sym (rightBol z y x) ⟩
  (((x ∙ z) ∙ y) ∙ z)  ∎
