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
0≤1 = 0≤x _

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
  1#           ≤⟨ x≤x+y _ _ ⟩
  1# + x ⋆ * x ≤⟨ starExpansiveˡ _ ⟩
  x ⋆ ∎

x≤xy⋆ : ∀ x y → x ≤ x * y ⋆
x≤xy⋆ x y = begin
  x       ≈⟨ *-identityʳ _ ⟨
  x * 1#  ≤⟨ *-monoˡ _ 1≤[ _ ]⋆ ⟩
  x * y ⋆ ∎

x≤y⋆x : ∀ x y → x ≤ y ⋆ * x
x≤y⋆x x y = begin
  x       ≈⟨ *-identityˡ _ ⟨
  1# * x  ≤⟨ *-monoʳ _ 1≤[ _ ]⋆ ⟩
  y ⋆ * x ∎

x≤y⇒xy⋆≤y⋆ : x ≤ y → x * y ⋆ ≤ y ⋆
x≤y⇒xy⋆≤y⋆ {x = x} {y = y} x≤y = begin
  x * y ⋆       ≤⟨ y≤x+y _ _ ⟩
  1# + x * y ⋆  ≤⟨ +-monoˡ _ (*-monoʳ _ x≤y) ⟩
  1# + y * y ⋆  ≤⟨ starExpansiveʳ _ ⟩
  y ⋆           ∎

x≤y⇒y⋆x≤y⋆ : x ≤ y → y ⋆ * x ≤ y ⋆
x≤y⇒y⋆x≤y⋆ {x = x} {y = y} x≤y = begin
  y ⋆ * x       ≤⟨ y≤x+y _ _ ⟩
  1# + y ⋆ * x  ≤⟨ +-monoˡ _ (*-monoˡ _ x≤y) ⟩
  1# + y ⋆ * y  ≤⟨ starExpansiveˡ _ ⟩
  y ⋆           ∎

xx⋆≤x⋆ : ∀ x → x * x ⋆ ≤ x ⋆
xx⋆≤x⋆ x = x≤y⇒xy⋆≤y⋆ ≤-refl

x⋆x≤x⋆ : ∀ x → x ⋆ * x ≤ x ⋆
x⋆x≤x⋆ x = x≤y⇒y⋆x≤y⋆ ≤-refl

x≤x⋆ : ∀ x → x ≤ x ⋆
x≤x⋆ x = begin
  x       ≈⟨ *-identityʳ _ ⟨
  x * 1#  ≤⟨ *-monoˡ _ 1≤[ _ ]⋆ ⟩
  x * x ⋆ ≤⟨ xx⋆≤x⋆ _ ⟩
  x ⋆     ∎

-- streamlined elimination rules

⋆-elimˡ : 1# ≤ x → y * x ≤ x → y ⋆ ≤ x
⋆-elimˡ {x = x} {y = y} 1≤x yx≤x = begin
  y ⋆       ≈⟨ *-identityʳ _ ⟨
  y ⋆ * 1#  ≤⟨ starDestructiveˡ _ _ _ (x≤z∧y≤z⇒[x+y]≤z 1≤x yx≤x) ⟩
  x         ∎

⋆-elimʳ : 1# ≤ x → x * y ≤ x → y ⋆ ≤ x
⋆-elimʳ {x = x} {y = y} 1≤x xy≤x = begin
  y ⋆       ≈⟨ *-identityˡ _ ⟨
  1# * y ⋆  ≤⟨ starDestructiveʳ _ _ _ (x≤z∧y≤z⇒[x+y]≤z 1≤x xy≤x) ⟩
  x         ∎

-- special cases for 0# and 1#

0⋆≤1 : 0# ⋆ ≤ 1#
0⋆≤1 = ⋆-elimˡ ≤-refl $ begin
  0# * 1# ≈⟨ zeroˡ _ ⟩
  0#      ≤⟨ 0≤1 ⟩
  1#      ∎

0⋆≈1 : 0# ⋆ ≈ 1#
0⋆≈1 = ≤-antisym 0⋆≤1 1≤[ _ ]⋆

1⋆≤1 : 1# ⋆ ≤ 1#
1⋆≤1 = ⋆-elimˡ ≤-refl $ ≤-reflexive (*-identityˡ _)

1⋆≈1 : 1# ⋆ ≈ 1#
1⋆≈1 = ≤-antisym 1⋆≤1 1≤[ _ ]⋆

-- _⋆ is monotonic and hence congruent

⋆-mono : Monotonic₁ _≤_ _≤_ _⋆
⋆-mono = ⋆-elimˡ 1≤[ _ ]⋆ ∘ x≤y⇒xy⋆≤y⋆

⋆-cong : Congruent _≈_ _≈_ _⋆
⋆-cong = mono⇒cong _≈_ _≈_ sym ≤-reflexive ≤-antisym ⋆-mono

-- _⋆ is idempotent

x⋆⋆≤x⋆ : ∀ x → (x ⋆) ⋆ ≤ x ⋆
x⋆⋆≤x⋆ x = ⋆-elimˡ 1≤[ _ ]⋆ $
  starDestructiveˡ _ _ _ (x≤z∧y≤z⇒[x+y]≤z ≤-refl (xx⋆≤x⋆ _))

x⋆≤x⋆⋆ : ∀ x → x ⋆ ≤ (x ⋆) ⋆
x⋆≤x⋆⋆ = ⋆-mono ∘ x≤x⋆

x⋆⋆≈x⋆ : ∀ x → (x ⋆) ⋆ ≈ x ⋆
x⋆⋆≈x⋆ x = ≤-antisym (x⋆⋆≤x⋆ x) (x⋆≤x⋆⋆ x)

-- commutation

xy≤yz⇒x⋆y≤yz⋆ : x * y ≤ y * z → x ⋆ * y ≤ y * z ⋆
xy≤yz⇒x⋆y≤yz⋆ {x = x} {y = y} {z = z} xy≤yz = starDestructiveˡ _ _ _ $
  x≤z∧y≤z⇒[x+y]≤z (x≤xy⋆ _ _) $ begin
    x * (y * z ⋆)  ≈⟨ *-assoc _ _ _ ⟨
    (x * y) * z ⋆  ≤⟨ *-monoʳ _ xy≤yz ⟩
    (y * z) * z ⋆  ≈⟨ *-assoc _ _ _ ⟩
    y * (z * z ⋆)  ≤⟨ *-monoˡ _ (xx⋆≤x⋆ _) ⟩
    y * z ⋆        ∎

yx≤zy⇒yx⋆≤z⋆y : y * x ≤ z * y → y * x ⋆ ≤ z ⋆ * y
yx≤zy⇒yx⋆≤z⋆y {y = y}{x = x} {z = z} yx≤zy = starDestructiveʳ _ _ _ $
  x≤z∧y≤z⇒[x+y]≤z (x≤y⋆x _ _) $ begin
    (z ⋆ * y) * x  ≈⟨ *-assoc _ _ _ ⟩
    z ⋆ * (y * x)  ≤⟨ *-monoˡ _ yx≤zy ⟩
    z ⋆ * (z * y)  ≈⟨ *-assoc _ _ _ ⟨
    (z ⋆ * z) * y  ≤⟨ *-monoʳ _ (x⋆x≤x⋆ _) ⟩
    z ⋆ * y        ∎

xy≈yz⇒x⋆y≈yz⋆ : x * y ≈ y * z → x ⋆ * y ≈ y * z ⋆
xy≈yz⇒x⋆y≈yz⋆ {x = x} {y = y} {z = z} xy≈yz = ≤-antisym
  (xy≤yz⇒x⋆y≤yz⋆ (≤-reflexive xy≈yz))
  (yx≤zy⇒yx⋆≤z⋆y (≤-reflexive (sym xy≈yz)))

-- Conway C17
[xy]⋆x≈x[yx]⋆ : ∀ x y → (x * y) ⋆ * x ≈ x * (y * x) ⋆
[xy]⋆x≈x[yx]⋆ x y = xy≈yz⇒x⋆y≈yz⋆ (*-assoc x y x)

{-

-- old proofs have been refactored in favour of the simpler combinations of the
-- above with the coproduct characterisation and the definition of the ordering
-- see also Conway's axiomatisation

-- Conway C11
[x+y]⋆≤[xy⋆]⋆*x⋆ : ∀ x y → (x + y) ⋆ ≤ (x * y ⋆) ⋆ * x ⋆
[x+y]⋆≤[xy⋆]⋆*x⋆ x y = {!!}

[xy⋆]⋆*x⋆≤[x+y]⋆ : ∀ x y → (x * y ⋆) ⋆ * x ⋆ ≤ (x + y) ⋆
[xy⋆]⋆*x⋆≤[x+y]⋆ x y = {!!}

[x+y]⋆≈[xy⋆]⋆*x⋆ : ∀ x y → (x + y) ⋆ ≈ (x * y ⋆) ⋆ * x ⋆
[x+y]⋆≈[xy⋆]⋆*x⋆ x y =
  ≤-antisym ([x+y]⋆≤[xy⋆]⋆*x⋆ x y) ([xy⋆]⋆*x⋆≤[x+y]⋆ x y)

-- Conway C12
[x*y]⋆≤1+x*[y*x]⋆*y : ∀ x y → (x * y) ⋆ ≤ 1# + x * (y * x) ⋆ * y
[x*y]⋆≤1+x*[y*x]⋆*y x y = {!!}

1+x*[y*x]⋆*y≤[x*y]⋆ : ∀ x y → 1# + x * (y * x) ⋆ * y ≤  (x * y) ⋆
1+x*[y*x]⋆*y≤[x*y]⋆ x y = {!!}

[x*y]⋆≈1+x*[y*x]⋆*y : ∀ x y → (x * y) ⋆ ≈ 1# + x * (y * x) ⋆ * y
[x*y]⋆≈1+x*[y*x]⋆*y x y =
  ≤-antisym ([x*y]⋆≤1+x*[y*x]⋆*y x y) (1+x*[y*x]⋆*y≤[x*y]⋆ x y)

-}
