------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (KleeneAlgebra)

module Algebra.Properties.KleeneAlgebra {k₁ k₂} (K : KleeneAlgebra k₁ k₂) where

open KleeneAlgebra K
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.PartialOrder poset as ≤-Reasoning


0⋆≈1 : 0# ⋆ ≈ 1#
0⋆≈1 = begin
  0# ⋆           ≈⟨ starExpansiveˡ 0# ⟨
  1# + 0# ⋆ * 0# ≈⟨ +-congˡ ( zeroʳ (0# ⋆)) ⟩
  1# + 0#        ≈⟨ +-identityʳ 1# ⟩
  1#             ∎

1+x⋆≈x⋆ : ∀ x → 1# + x ⋆ ≈ x ⋆
1+x⋆≈x⋆ x = sym (begin
  x ⋆                   ≈⟨ starExpansiveʳ x ⟨
  1# + x * x ⋆          ≈⟨ +-congʳ (+-idem 1#) ⟨
  1# + 1# + x * x ⋆     ≈⟨ +-assoc 1# 1# ((x * x ⋆ )) ⟩
  1# + (1# + x * x ⋆)   ≈⟨ +-congˡ (starExpansiveʳ x) ⟩
  1# + x ⋆              ∎)

x⋆+xx⋆≈x⋆ : ∀ x → x ⋆ + x * x ⋆ ≈ x ⋆
x⋆+xx⋆≈x⋆ x = begin
  x ⋆ + x * x ⋆         ≈⟨ +-congʳ (1+x⋆≈x⋆ x) ⟨
  1# + x ⋆ + x * x ⋆    ≈⟨ +-congʳ (+-comm 1# ((x ⋆))) ⟩
  x ⋆ + 1# + x * x ⋆    ≈⟨ +-assoc ((x ⋆)) 1# ((x * x ⋆ )) ⟩
  x ⋆ + (1# + x * x ⋆)  ≈⟨ +-congˡ (starExpansiveʳ x) ⟩
  x ⋆ + x ⋆             ≈⟨ +-idem (x ⋆) ⟩
  x ⋆                   ∎

x⋆+x⋆x≈x⋆ : ∀ x → x ⋆ + x ⋆ * x ≈ x ⋆
x⋆+x⋆x≈x⋆ x = begin
  x ⋆ + x ⋆ * x         ≈⟨ +-congʳ (1+x⋆≈x⋆ x) ⟨
  1# + x ⋆ + x ⋆ * x    ≈⟨ +-congʳ (+-comm 1# (x ⋆)) ⟩
  x ⋆ + 1# + x ⋆ * x    ≈⟨ +-assoc (x ⋆) 1# (x ⋆ * x) ⟩
  x ⋆ + (1# + x ⋆ * x)  ≈⟨ +-congˡ (starExpansiveˡ x) ⟩
  x ⋆ + x ⋆             ≈⟨ +-idem (x ⋆) ⟩
  x ⋆                   ∎

x+x⋆≈x⋆ : ∀ x → x + x ⋆ ≈ x ⋆
x+x⋆≈x⋆ x = begin
  x + x ⋆                  ≈⟨ +-congˡ (starExpansiveʳ x) ⟨
  x + (1# + x * x ⋆)       ≈⟨ +-congʳ (*-identityʳ x) ⟨
  x * 1# + (1# + x * x ⋆)  ≈⟨ +-assoc (x * 1#) 1# (x * x ⋆) ⟨
  x * 1# + 1# + x * x ⋆    ≈⟨ +-congʳ (+-comm (x * 1#) 1#) ⟩
  1# + x * 1# + x * x ⋆    ≈⟨ +-assoc 1# (x * 1#) (x * x ⋆) ⟩
  1# + (x * 1# + x * x ⋆)  ≈⟨ +-congˡ (distribˡ x 1# ((x ⋆))) ⟨
  1# + x * (1# + x ⋆)      ≈⟨ +-congˡ (*-congˡ (1+x⋆≈x⋆ x)) ⟩
  1# + x * x ⋆             ≈⟨ (starExpansiveʳ x) ⟩
  x ⋆                      ∎

1+x+x⋆≈x⋆ : ∀ x → 1# + x + x ⋆ ≈ x ⋆
1+x+x⋆≈x⋆ x = begin
  1# + x + x ⋆    ≈⟨ +-assoc 1# x (x ⋆) ⟩
  1# + (x + x ⋆)  ≈⟨ +-congˡ (x+x⋆≈x⋆ x) ⟩
  1# + x ⋆        ≈⟨ 1+x⋆≈x⋆ x ⟩
  x ⋆             ∎

0+x+x⋆≈x⋆ : ∀ x → 0# + x + x ⋆ ≈ x ⋆
0+x+x⋆≈x⋆ x = begin
  0# + x + x ⋆    ≈⟨ +-assoc 0# x (x ⋆) ⟩
  0# + (x + x ⋆)  ≈⟨ +-identityˡ ((x + x ⋆)) ⟩
  (x + x ⋆)       ≈⟨ x+x⋆≈x⋆ x ⟩
  x ⋆             ∎

x⋆x⋆≈x⋆ : ∀ x → x ⋆ * x ⋆ ≈ x ⋆
x⋆x⋆≈x⋆ x = starDestructiveˡ x (x ⋆) (x ⋆) (x⋆+xx⋆≈x⋆ x)

1+x⋆x⋆≈x⋆ : ∀ x → 1# + x ⋆ * x ⋆ ≈ x ⋆
1+x⋆x⋆≈x⋆ x = begin
  1# + x ⋆ * x ⋆  ≈⟨ +-congˡ (x⋆x⋆≈x⋆ x) ⟩
  1# + x ⋆        ≈⟨ 1+x⋆≈x⋆ x ⟩
  x ⋆             ∎

x⋆⋆≈x⋆ : ∀ x → (x ⋆) ⋆ ≈ x ⋆
x⋆⋆≈x⋆ x = begin
  (x ⋆) ⋆        ≈⟨ *-identityʳ ((x ⋆) ⋆) ⟨
  (x ⋆) ⋆ * 1#   ≈⟨ starDestructiveˡ (x ⋆) 1# (x ⋆) (1+x⋆x⋆≈x⋆ x) ⟩
  x ⋆            ∎

1+11≈1 : 1# + 1# * 1# ≈ 1#
1+11≈1 = begin
  1# + 1# * 1#  ≈⟨ +-congˡ ( *-identityʳ 1#) ⟩
  1# + 1#       ≈⟨ +-idem 1# ⟩
  1#            ∎

1⋆≈1 : 1# ⋆ ≈ 1#
1⋆≈1 = begin
  1# ⋆       ≈⟨ *-identityʳ (1# ⋆) ⟨
  1# ⋆ * 1#  ≈⟨ starDestructiveˡ 1# 1# 1# 1+11≈1 ⟩
  1#         ∎

x≈y⇒1+xy⋆≈y⋆ : ∀ x y → x ≈  y → 1# + x * y ⋆ ≈ y ⋆
x≈y⇒1+xy⋆≈y⋆ x y eq = begin
  1# + x * y ⋆  ≈⟨ +-congˡ (*-congʳ (eq)) ⟩
  1# + y * y ⋆  ≈⟨ starExpansiveʳ y ⟩
  y ⋆           ∎

x≈y⇒x⋆≈y⋆ : ∀ x y → x ≈ y → x ⋆ ≈ y ⋆
x≈y⇒x⋆≈y⋆ x y eq = begin
  x ⋆       ≈⟨ *-identityʳ (x ⋆) ⟨
  x ⋆ * 1#  ≈⟨ (starDestructiveˡ x 1# (y ⋆) (x≈y⇒1+xy⋆≈y⋆ x y eq)) ⟩
  y ⋆       ∎

ax≈xb⇒x+axb⋆≈xb⋆ : ∀ x a b → a * x ≈ x * b → x + a * (x * b ⋆) ≈ x * b ⋆
ax≈xb⇒x+axb⋆≈xb⋆ x a b eq = begin
  x + a * (x * b ⋆)       ≈⟨ +-congˡ (*-assoc a x (b ⋆)) ⟨
  x + a * x * b ⋆         ≈⟨ +-congʳ (*-identityʳ x) ⟨
  x * 1# + a * x * b ⋆    ≈⟨ +-congˡ (*-congʳ (eq)) ⟩
  x * 1# + x * b * b ⋆    ≈⟨ +-congˡ (*-assoc x b (b ⋆) ) ⟩
  x * 1# + x * (b * b ⋆)  ≈⟨ distribˡ x 1# (b * b ⋆) ⟨
  x * (1# + b * b ⋆)      ≈⟨ *-congˡ (starExpansiveʳ b) ⟩
  x * b ⋆                 ∎

ax≈xb⇒a⋆x≈xb⋆ : ∀ x a b → a * x ≈ x * b → a ⋆ * x ≈ x * b ⋆
ax≈xb⇒a⋆x≈xb⋆ x a b eq = starDestructiveˡ a x ((x * b ⋆)) (ax≈xb⇒x+axb⋆≈xb⋆ x a b eq)

[xy]⋆x≈x[yx]⋆ : ∀ x y → (x * y) ⋆ * x ≈ x * (y * x) ⋆
[xy]⋆x≈x[yx]⋆ x y = ax≈xb⇒a⋆x≈xb⋆ x (x * y) (y * x) (*-assoc x y x)
