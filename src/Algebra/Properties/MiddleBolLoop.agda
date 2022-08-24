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

yx\x≈x\y\x : ∀ x y → ((y ∙ x) \\ x) ≈ (x \\ (y \\ x))
yx\x≈x\y\x x y = begin
  ((y ∙ x) \\ x) ≈⟨ \\-congʳ(sym (identityˡ _)) ⟩ 
  {!   !} ≈⟨ {! leftDividesˡ ?  ?  !} ⟩

  (x \\ (y \\ x)) ∎