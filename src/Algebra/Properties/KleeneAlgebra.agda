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

0⋆≈1 : 0# ⋆ ≈ 1#
0⋆≈1 = begin
  0# ⋆           ≈⟨ sym (starExpansiveˡ 0#) ⟩
  1# + 0# ⋆ * 0# ≈⟨ +-congˡ ( zeroʳ (0# ⋆)) ⟩
  1# + 0#        ≈⟨ +-identityʳ 1# ⟩
  1#             ∎

1+x⋆≈x⋆ : ∀ x → 1# + x ⋆ ≈ x ⋆
1+x⋆≈x⋆ x = sym (begin
  x ⋆                   ≈⟨ sym (starExpansiveʳ x) ⟩ 
  1# + x * x ⋆          ≈⟨ +-congʳ (sym (+-idem 1#)) ⟩ 
  (1# + 1#) + x * x ⋆   ≈⟨ +-assoc _ _ _ ⟩ 
  1# + (1# + x * x ⋆)   ≈⟨ +-congˡ (starExpansiveʳ x) ⟩  
  1# + x ⋆              ∎)

x⋆+xx⋆≈x⋆ : ∀ x → x ⋆ + x * x ⋆ ≈ x ⋆ 
x⋆+xx⋆≈x⋆ x = begin
  x ⋆ + x * x ⋆         ≈⟨ +-congʳ (sym (1+x⋆≈x⋆ x)) ⟩
  1# + x ⋆ + x * x ⋆    ≈⟨ +-congʳ (+-comm _ _) ⟩
  x ⋆ + 1# + x * x ⋆    ≈⟨ +-assoc _ _ _ ⟩
  x ⋆ + (1# + x * x ⋆)  ≈⟨ +-congˡ (starExpansiveʳ x) ⟩ 
  x ⋆ + x ⋆             ≈⟨ +-idem _ ⟩ 
  x ⋆                   ∎

x⋆+x⋆x≈x⋆ : ∀ x → x ⋆ + x ⋆ * x ≈ x ⋆ 
x⋆+x⋆x≈x⋆ x = begin
  x ⋆ + x ⋆ * x         ≈⟨ +-congʳ (sym (1+x⋆≈x⋆ x)) ⟩ 
  1# + x ⋆ + x ⋆ * x    ≈⟨ +-congʳ (+-comm _ _) ⟩ 
  x ⋆ + 1# + x ⋆ * x    ≈⟨ +-assoc _ _ _ ⟩ 
  x ⋆ + (1# + x ⋆ * x)  ≈⟨ +-congˡ (starExpansiveˡ x) ⟩  
  x ⋆ + x ⋆             ≈⟨ +-idem _ ⟩ 
  x ⋆                   ∎

x+x⋆≈x⋆ : ∀ x → x + x ⋆ ≈ x ⋆ 
x+x⋆≈x⋆ x = begin
  x + x ⋆                  ≈⟨ +-congˡ (sym (starExpansiveʳ x)) ⟩ 
  x + (1# + x * x ⋆)       ≈⟨ +-congʳ (sym (*-identityʳ x)) ⟩ 
  x * 1# + (1# + x * x ⋆)  ≈⟨ sym (+-assoc _ _ _) ⟩ 
  x * 1# + 1# + x * x ⋆    ≈⟨ +-congʳ (+-comm _ _) ⟩ 
  1# + x * 1# + x * x ⋆    ≈⟨ +-assoc _ _ _ ⟩ 
  1# + (x * 1# + x * x ⋆)  ≈⟨ +-congˡ (sym (distribˡ _ _ _)) ⟩ 
  1# + x * (1# + x ⋆)      ≈⟨ +-congˡ (*-congˡ (1+x⋆≈x⋆ _)) ⟩ 
  1# + x * x ⋆             ≈⟨ (starExpansiveʳ _) ⟩ 
  x ⋆                      ∎ 

1+x+x⋆≈x⋆ : ∀ x → 1# + x + x ⋆ ≈ x ⋆
1+x+x⋆≈x⋆ x = begin
  1# + x + x ⋆    ≈⟨ +-assoc _ _ _ ⟩ 
  1# + (x + x ⋆)  ≈⟨ +-congˡ (x+x⋆≈x⋆ x) ⟩ 
  1# + x ⋆        ≈⟨ 1+x⋆≈x⋆ _ ⟩
  x ⋆             ∎

0+x+x⋆≈x⋆ : ∀ x → 0# + x + x ⋆ ≈ x ⋆
0+x+x⋆≈x⋆ x = begin
  0# + x + x ⋆    ≈⟨ +-assoc _ _ _ ⟩ 
  0# + (x + x ⋆)  ≈⟨ +-identityˡ _ ⟩ 
  (x + x ⋆)       ≈⟨ x+x⋆≈x⋆ x ⟩ 
  x ⋆             ∎
