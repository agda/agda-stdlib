------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (KleeneAlgebra)

module Algebra.Properties.KleeneAlgebra {k₁ k₂} (K : KleeneAlgebra k₁ k₂) where

open import Function.Base using (_$_)
open import Relation.Binary.Definitions
  using (Monotonic₁; Monotonic₂)

open KleeneAlgebra K renaming (Carrier to A)
open import Algebra.Definitions _≈_
open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup
  using (medial)
open import Relation.Binary.Reasoning.PartialOrder poset as ≤-Reasoning

private
  variable
    x y z : A


------------------------------------------------------------------------
-- _+_ is monotonic in both arguments

+-mono : Monotonic₂ _≤_ _≤_ _≤_ _+_
+-mono {x = x} {y = y} {u = u} {v = v} x≤y u≤v = begin-equality
 (x + u) + (y + v) ≈⟨ medial x u y v ⟩
 (x + y) + (u + v) ≈⟨ +-cong x≤y u≤v ⟩
 y + v       ∎

------------------------------------------------------------------------
-- 0# is initial

0≤x : ∀ x → 0# ≤ x
0≤x = +-identityˡ

0≤1 : 0# ≤ 1#
0≤1 = 0≤x 1#

------------------------------------------------------------------------
-- x + y is a coproduct/least upper bound

x≤x+y : ∀ x y → x ≤ x + y
x≤x+y x y = begin-equality
 x + (x + y) ≈⟨ +-assoc x x y ⟨
 (x + x) + y ≈⟨ +-congʳ (+-idem x) ⟩
 x + y       ∎

y≤x+y : ∀ x y → y ≤ x + y
y≤x+y x y = begin-equality
 y + (x + y) ≈⟨ +-congˡ (+-comm x y) ⟩
 y + (y + x) ≈⟨ x≤x+y y x ⟩
 y + x ≈⟨ +-comm x y ⟨
 x + y ∎

x≤z∧y≤z⇒[x+y]≤z : x ≤ z → y ≤ z → x + y ≤ z
x≤z∧y≤z⇒[x+y]≤z {x = x} {z = z} {y = y} x≤z y≤z = begin-equality
 (x + y) + z ≈⟨ +-assoc x y z ⟩
 x + (y + z) ≈⟨ +-congˡ y≤z ⟩
 x + z ≈⟨ x≤z ⟩
 z ∎

------------------------------------------------------------------------
-- _⋆

1≤[_]⋆ : ∀ x → 1# ≤ x ⋆
1≤[ x ]⋆ = begin
    1#           ≤⟨ x≤x+y 1# _ ⟩
    1# + x ⋆ * x ≤⟨ starExpansiveˡ x ⟩
    x ⋆ ∎

0⋆≈1 : 0# ⋆ ≈ 1#
0⋆≈1 = ≤-antisym
  (begin
    0# ⋆           ≈⟨ *-identityʳ _ ⟨
    0# ⋆ * 1#      ≤⟨ starDestructiveˡ _ _ _ $
                      (x≤z∧y≤z⇒[x+y]≤z ≤-refl $ begin
                         0# * 1# ≈⟨ zeroˡ 1# ⟩
                         0#      ≤⟨ 0≤1 ⟩
                         1#      ∎
                      ) ⟩
    1#             ∎)
  1≤[ 0# ]⋆

1⋆*[_]≈1 : ∀ x → 1# ⋆ * x ≤ x
1⋆*[ x ]≈1 = starDestructiveˡ _ _ _ $
               x≤z∧y≤z⇒[x+y]≤z ≤-refl (≤-reflexive (*-identityˡ _))

1⋆≈1 : 1# ⋆ ≈ 1#
1⋆≈1 = ≤-antisym
  (begin
    (1# ⋆)    ≈⟨ *-identityʳ _ ⟨
    1# ⋆ * 1# ≤⟨ 1⋆*[ 1# ]≈1 ⟩
    1#        ∎)
  1≤[ 1# ]⋆

1+x⋆≈x⋆ : ∀ x → 1# + x ⋆ ≈ x ⋆
1+x⋆≈x⋆ x = ≤-antisym (x≤z∧y≤z⇒[x+y]≤z 1≤[ x ]⋆ ≤-refl) (y≤x+y _ _)

{-
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
-}
