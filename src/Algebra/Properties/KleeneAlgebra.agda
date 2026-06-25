------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (KleeneAlgebra)

module Algebra.Properties.KleeneAlgebra {k₁ k₂} (K : KleeneAlgebra k₁ k₂) where

open import Function.Base using (_∘_; _$_)
open import Function.Definitions using (Congruent)
open import Relation.Binary.Consequences
  using (mono₂⇒monoˡ; mono₂⇒monoʳ; monoˡ∧monoʳ⇒mono₂; mono⇒cong)
open import Relation.Binary.Definitions
  using (LeftMonotonic; RightMonotonic; Monotonic₁; Monotonic₂)

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

+-monoˡ : LeftMonotonic _≤_ _≤_ _+_
+-monoˡ = mono₂⇒monoˡ _≤_ _≤_ _≤_ ≤-refl +-mono

+-monoʳ : RightMonotonic _≤_ _≤_ _+_
+-monoʳ = mono₂⇒monoʳ _≤_ _≤_ _≤_ ≤-refl +-mono

------------------------------------------------------------------------
-- _*_ is monotonic in both arguments

*-monoˡ : LeftMonotonic _≤_ _≤_ _*_
*-monoˡ z {x = x} {y = y} x≤y = begin-equality
  z * x + z * y ≈⟨ distribˡ z x y ⟨
  z * (x + y)   ≈⟨ *-congˡ x≤y ⟩
  z * y ∎

*-monoʳ : RightMonotonic _≤_ _≤_ _*_
*-monoʳ z {x = x} {y = y} x≤y = begin-equality
  x * z + y * z ≈⟨ distribʳ z x y ⟨
  (x + y) * z   ≈⟨ *-congʳ x≤y ⟩
  y * z ∎

*-mono : Monotonic₂ _≤_ _≤_ _≤_ _*_
*-mono = monoˡ∧monoʳ⇒mono₂ _≤_ _≤_ _≤_ ≤-trans *-monoˡ *-monoʳ

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

-- streamlined introduction rules

1≤[_]⋆ : ∀ x → 1# ≤ x ⋆
1≤[ x ]⋆ = begin
  1#           ≤⟨ x≤x+y 1# _ ⟩
  1# + x ⋆ * x ≤⟨ starExpansiveˡ x ⟩
  x ⋆ ∎

x≤y⇒xy⋆≤y⋆ : x ≤ y → x * y ⋆ ≤ y ⋆
x≤y⇒xy⋆≤y⋆ {x = x} {y = y} x≤y = begin
  x * y ⋆       ≤⟨ y≤x+y _ _ ⟩
  1# + x * y ⋆  ≤⟨ +-monoˡ _ (*-monoʳ _ x≤y) ⟩
  1# + y * y ⋆  ≤⟨ starExpansiveʳ y ⟩
  y ⋆           ∎

x≤y⇒y⋆x≤y⋆ : x ≤ y → y ⋆ * x ≤ y ⋆
x≤y⇒y⋆x≤y⋆ {x = x} {y = y} x≤y = begin
  y ⋆ * x       ≤⟨ y≤x+y _ _ ⟩
  1# + y ⋆ * x  ≤⟨ +-monoˡ _ (*-monoˡ _ x≤y) ⟩
  1# + y ⋆ * y  ≤⟨ starExpansiveˡ y ⟩
  y ⋆           ∎

xx⋆≤x⋆ : ∀ x → x * x ⋆ ≤ x ⋆
xx⋆≤x⋆ x = x≤y⇒xy⋆≤y⋆ ≤-refl

x⋆x≤x⋆ : ∀ x → x ⋆ * x ≤ x ⋆
x⋆x≤x⋆ x = x≤y⇒y⋆x≤y⋆ ≤-refl

x≤x⋆ : ∀ x → x ≤ x ⋆
x≤x⋆ x = begin
  x       ≈⟨ *-identityʳ _ ⟨
  x * 1#  ≤⟨ *-monoˡ x 1≤[ x ]⋆ ⟩
  x * x ⋆ ≤⟨ xx⋆≤x⋆ x ⟩
  x ⋆     ∎ 

-- streamlined elimination rules

⋆-elimˡ : ∀ x → 1# ≤ y → x * y ≤ y → x ⋆ ≤ y
⋆-elimˡ {y = y} x 1≤y x*y≤y = begin
  x ⋆       ≈⟨ *-identityʳ _ ⟨
  x ⋆ * 1#  ≤⟨ starDestructiveˡ _ _ _ (x≤z∧y≤z⇒[x+y]≤z 1≤y x*y≤y) ⟩
  y         ∎

⋆-elimʳ : ∀ x → 1# ≤ y → y * x ≤ y → x ⋆ ≤ y
⋆-elimʳ {y = y} x 1≤y y*x≤y = begin
  x ⋆       ≈⟨ *-identityˡ _ ⟨
  1# * x ⋆  ≤⟨ starDestructiveʳ _ _ _ (x≤z∧y≤z⇒[x+y]≤z 1≤y y*x≤y) ⟩
  y         ∎

-- special cases for 0# and 1#

0⋆≤1 : 0# ⋆ ≤ 1#
0⋆≤1 = ⋆-elimˡ 0# ≤-refl $ begin
  0# * 1# ≈⟨ zeroˡ 1# ⟩
  0#      ≤⟨ 0≤1 ⟩
  1#      ∎

0⋆≈1 : 0# ⋆ ≈ 1#
0⋆≈1 = ≤-antisym 0⋆≤1 1≤[ 0# ]⋆

1⋆≤1 : 1# ⋆ ≤ 1#
1⋆≤1 = ⋆-elimˡ 1# ≤-refl (≤-reflexive (*-identityˡ _))

1⋆≈1 : 1# ⋆ ≈ 1#
1⋆≈1 = ≤-antisym 1⋆≤1 1≤[ 1# ]⋆

-- _⋆ is monotonic and hence congruent

⋆-mono : Monotonic₁ _≤_ _≤_ _⋆
⋆-mono = ⋆-elimˡ _ 1≤[ _ ]⋆ ∘ x≤y⇒xy⋆≤y⋆

⋆-cong : Congruent _≈_ _≈_ _⋆
⋆-cong = mono⇒cong _≈_ _≈_ sym ≤-reflexive ≤-antisym ⋆-mono

-- _⋆ is idempotent

x⋆⋆≤x⋆ : ∀ x → (x ⋆) ⋆ ≤ x ⋆
x⋆⋆≤x⋆ x = ⋆-elimˡ (x ⋆) 1≤[ _ ]⋆ $ 
  starDestructiveˡ _ _ _ (x≤z∧y≤z⇒[x+y]≤z ≤-refl (xx⋆≤x⋆ _))

x⋆≤x⋆⋆ : ∀ x → x ⋆ ≤ (x ⋆) ⋆
x⋆≤x⋆⋆ = ⋆-mono ∘ x≤x⋆

x⋆⋆≈x⋆ : ∀ x → (x ⋆) ⋆ ≈ x ⋆
x⋆⋆≈x⋆ x = ≤-antisym (x⋆⋆≤x⋆ x) (x⋆≤x⋆⋆ x)

{-
-- removed from consideration!
-- most of these seem eliminable in favour of the simpler combinations of
-- above of the coproduct characterisation and the definition of the ordering
-- see also Conway's axiomatisation

-- eg
1+x⋆≈x⋆ : ∀ x → 1# + x ⋆ ≈ x ⋆
1+x⋆≈x⋆ x = 1≤[ x ]⋆

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
