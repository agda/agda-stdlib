------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles

module Algebra.Properties.KleeneAlgebra {k₁ k₂} (K : KleeneAlgebra k₁ k₂) where

open KleeneAlgebra K
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid setoid
open import Function
open import Data.Product

0⋆≈1 : 0# ⋆ ≈ 1#
0⋆≈1 = begin 
  0# ⋆ ≈⟨ sym (starExpansiveˡ 0#) ⟩ 
  1# + 0# ⋆ * 0# ≈⟨ +-congˡ ( zeroʳ (0# ⋆)) ⟩
  1# + 0# ≈⟨ +-identityʳ 1# ⟩
  1# ∎