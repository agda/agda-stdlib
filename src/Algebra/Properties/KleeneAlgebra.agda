------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties of Kleene Algebra based on Kozen
--
-- Old proofs in the library have been heavily refactored in favour
-- of simpler combinations of admissible introduction and elimination
-- rules, together with the coproduct characterisation of _+_ and the
-- equational definition of the ordering x ≤ y = x + y ≈ y
--
-- For comparison with earlier approaches, see also Conway's axiomatisation
-- in "Regular Algebra and Finite Machines" (Chapman and Hall, 1971)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (KleeneAlgebra)

module Algebra.Properties.KleeneAlgebra {c ℓ} (K : KleeneAlgebra c ℓ) where

open import Function.Base using (_∘_; _$_)
open import Relation.Binary.Bundles using (Preorder; Poset)
open import Relation.Binary.Consequences
  using (mono₂⇒monoˡ; mono₂⇒monoʳ; monoˡ∧monoʳ⇒mono₂; mono⇒cong)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; Antisymmetric
        ; LeftMonotonic; RightMonotonic; Monotonic₁; Monotonic₂)
import Relation.Binary.Reasoning.PartialOrder as ≤-Reasoning
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Structures using (IsPreorder; IsPartialOrder)

open KleeneAlgebra K renaming (Carrier to A)
open import Algebra.Definitions _≈_
open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup
  using (medial)
open import Algebra.Properties.Semigroup *-semigroup
  using (x∙yz≈xy∙z)

private
  variable
    x y z : A


------------------------------------------------------------------------
-- Basic properties of the _≤_ Kleene ordering
--
-- 1. That it does admit an IsPartialOrder structure/Poset bundle
-- 2. That the algebraic operations are monotone for the ordering
-- 3. That (0, _+_) define finite coproduct structure on _≤_

module _ where

  open ≈-Reasoning setoid

  ≤-reflexive : _≈_ ⇒ _≤_
  ≤-reflexive {x = x} {y = y} x≈y = begin
    x + y ≈⟨ +-congʳ x≈y ⟩
    y + y ≈⟨ +-idem _ ⟩
    y     ∎

  ≤-refl : Reflexive _≤_
  ≤-refl = ≤-reflexive refl

  ≤-trans : Transitive _≤_
  ≤-trans {x = x} {y = y} {z = z} x+y≈y y+z≈z = begin
    x + z        ≈⟨ +-congˡ y+z≈z ⟨
    x + (y + z)  ≈⟨ +-assoc _ _ _ ⟨
    (x + y) + z  ≈⟨ +-congʳ x+y≈y ⟩
    y + z        ≈⟨ y+z≈z ⟩
    z ∎

  ≤-antisym : Antisymmetric _≈_ _≤_
  ≤-antisym {x = x} {y = y} x+y≈y y+x≈x = begin
    x     ≈⟨ y+x≈x ⟨
    y + x ≈⟨ +-comm y x ⟩
    x + y ≈⟨ x+y≈y ⟩
    y     ∎

  isPreorder : IsPreorder _≈_ _≤_
  isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = ≤-reflexive
    ; trans = ≤-trans
    }

  isPartialOrder : IsPartialOrder _≈_ _≤_
  isPartialOrder = record
    { isPreorder = isPreorder
    ; antisym = ≤-antisym
    }

  preorder : Preorder _ _ _
  preorder = record { isPreorder = isPreorder }

  poset : Poset _ _ _
  poset = record { isPartialOrder = isPartialOrder }

------------------------------------------------------------------------
-- _+_ is monotonic in both arguments

  +-mono : Monotonic₂ _≤_ _≤_ _≤_ _+_
  +-mono {x = x} {y = y} {u = u} {v = v} x≤y u≤v = begin
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
  *-monoˡ z {x = x} {y = y} x≤y = begin
    z * x + z * y ≈⟨ distribˡ z x y ⟨
    z * (x + y)   ≈⟨ *-congˡ x≤y ⟩
    z * y ∎

  *-monoʳ : RightMonotonic _≤_ _≤_ _*_
  *-monoʳ z {x = x} {y = y} x≤y = begin
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
  x≤x+y x y = begin
   x + (x + y) ≈⟨ +-assoc x x y ⟨
   (x + x) + y ≈⟨ +-congʳ (+-idem x) ⟩
   x + y       ∎

  y≤x+y : ∀ x y → y ≤ x + y
  y≤x+y x y = begin
   y + (x + y) ≈⟨ +-congˡ (+-comm x y) ⟩
   y + (y + x) ≈⟨ x≤x+y y x ⟩
   y + x       ≈⟨ +-comm x y ⟨
   x + y       ∎

  x≤z∧y≤z⇒[x+y]≤z : x ≤ z → y ≤ z → x + y ≤ z
  x≤z∧y≤z⇒[x+y]≤z {x = x} {z = z} {y = y} x≤z y≤z = begin
   (x + y) + z ≈⟨ +-assoc x y z ⟩
   x + (y + z) ≈⟨ +-congˡ y≤z ⟩
   x + z       ≈⟨ x≤z ⟩
   z           ∎

------------------------------------------------------------------------
-- _⋆

-- Now, work relative to ≤-Reasoning

open ≤-Reasoning poset

-- streamlined introduction rules and their corollaries

1≤[_]⋆ : ∀ x → 1# ≤ x ⋆
1≤[ x ]⋆ = begin
  1#           ≤⟨ x≤x+y _ _ ⟩
  1# + x ⋆ * x ≤⟨ starExpansiveˡ _ ⟩
  x ⋆          ∎

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

⋆-*-elimˡ : x * y ≤ y → x ⋆ * y ≤ y
⋆-*-elimˡ = starDestructiveˡ _ _ _ ∘ x≤z∧y≤z⇒[x+y]≤z ≤-refl

⋆-*-elimʳ : y * x ≤ y → y * x ⋆ ≤ y
⋆-*-elimʳ = starDestructiveʳ _ _ _ ∘ x≤z∧y≤z⇒[x+y]≤z ≤-refl

1+x⋆≈x⋆ : ∀ x → 1# + x ⋆ ≈ x ⋆
1+x⋆≈x⋆ x = ≤-antisym (x≤z∧y≤z⇒[x+y]≤z 1≤[ _ ]⋆ ≤-refl) (y≤x+y _ _)

x⋆≈1+xx⋆ : ∀ x → x ⋆ ≈ 1# + x * x ⋆
x⋆≈1+xx⋆ x = ≤-antisym (⋆-elimˡ (x≤x+y _ _) $ begin
  x * (1# + x * x ⋆)     ≤⟨ *-monoˡ _ $ +-monoˡ _ $ xx⋆≤x⋆ _ ⟩
  x * (1# + x ⋆)         ≈⟨ *-congˡ (1+x⋆≈x⋆ _) ⟩
  x * x ⋆                ≤⟨ y≤x+y _ _ ⟩
  1# + x * x ⋆           ∎) $ starExpansiveʳ _

x⋆≈1+x⋆x : ∀ x → x ⋆ ≈ 1# + x ⋆ * x
x⋆≈1+x⋆x x = ≤-antisym (⋆-elimʳ (x≤x+y _ _) $ begin
  (1# + x ⋆ * x) * x     ≤⟨ *-monoʳ _ $ +-monoˡ _ $ x⋆x≤x⋆ _ ⟩
  (1# + x ⋆) * x         ≈⟨ *-congʳ (1+x⋆≈x⋆ _) ⟩
  x ⋆ * x                ≤⟨ y≤x+y _ _ ⟩
  1# + x ⋆ * x           ∎) $ starExpansiveˡ _

{- FAILS: parser falls over
  begin-equality
  x ⋆ ≈⟨ {!!} ⟨⟩ ? ⟩
  {!!} ≈⟨ {!!} ⟩
  1# + x ⋆ * x ∎
-}

-- special cases for 0# and 1#

0⋆≤1 : 0# ⋆ ≤ 1#
0⋆≤1 = ⋆-elimˡ ≤-refl $ begin
  0# * 1# ≈⟨ zeroˡ _ ⟩
  0#      ≤⟨ 0≤1 ⟩
  1#      ∎

0⋆≈1 : 0# ⋆ ≈ 1#
0⋆≈1 = ≤-antisym 0⋆≤1 1≤[ _ ]⋆

1⋆≤1 : 1# ⋆ ≤ 1#
1⋆≤1 = ⋆-elimˡ ≤-refl $ ≤-reflexive $ *-identityˡ _

1⋆≈1 : 1# ⋆ ≈ 1#
1⋆≈1 = ≤-antisym 1⋆≤1 1≤[ _ ]⋆

-- _⋆ is monotonic, and hence congruent for _≈_

⋆-mono : Monotonic₁ _≤_ _≤_ _⋆
⋆-mono = ⋆-elimˡ 1≤[ _ ]⋆ ∘ x≤y⇒xy⋆≤y⋆

⋆-cong : Congruent₁ _⋆
⋆-cong = mono⇒cong _≈_ _≈_ sym ≤-reflexive ≤-antisym ⋆-mono

-- _⋆ is idempotent

x⋆x⋆≤x⋆ : ∀ x → x ⋆ * x ⋆ ≤ x ⋆
x⋆x⋆≤x⋆ = ⋆-*-elimˡ ∘ xx⋆≤x⋆

x⋆⋆≤x⋆ : ∀ x → (x ⋆) ⋆ ≤ x ⋆
x⋆⋆≤x⋆ = ⋆-elimˡ 1≤[ _ ]⋆ ∘ x⋆x⋆≤x⋆

x⋆≤x⋆⋆ : ∀ x → x ⋆ ≤ (x ⋆) ⋆
x⋆≤x⋆⋆ = ⋆-mono ∘ x≤x⋆

x⋆⋆≈x⋆ : ∀ x → (x ⋆) ⋆ ≈ x ⋆
x⋆⋆≈x⋆ x = ≤-antisym (x⋆⋆≤x⋆ x) (x⋆≤x⋆⋆ x)

-- distributive laws

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

-- a useful absorption property

xy≤y∧xz≤z⇒xy⋆z≤y⋆z : x * y ≤ y → x * z ≤ z → x * y ⋆ * z ≤ y ⋆ * z
xy≤y∧xz≤z⇒xy⋆z≤y⋆z {x = x} {y = y} {z = z} xy≤y xz≤z = begin
  x * y ⋆ * z ≈⟨ *-congʳ $ *-congˡ $ x⋆≈1+xx⋆ _ ⟩
  x * (1# + y * y ⋆) * z       ≈⟨ *-congʳ $ distribˡ _ _ _ ⟩
  (x * 1# + x * (y * y ⋆)) * z ≈⟨ *-congʳ $ +-cong (*-identityʳ _) (x∙yz≈xy∙z _ _ _) ⟩
  (x + x * y * y ⋆) * z        ≈⟨ distribʳ _ _ _ ⟩
  x * z + x * y * y ⋆ * z      ≤⟨ +-mono xz≤z (*-monoʳ _ $  *-monoʳ _ xy≤y) ⟩
  z + y * y ⋆ * z              ≈⟨ +-congʳ $ *-identityˡ _ ⟨
  1# * z + y * y ⋆ * z         ≈⟨ distribʳ _ _ _ ⟨
  (1# + y * y ⋆) * z           ≈⟨ *-congʳ $ x⋆≈1+xx⋆ _ ⟨
  y ⋆ * z ∎

-- Conway C17

[xy]⋆x≈x[yx]⋆ : ∀ x y → (x * y) ⋆ * x ≈ x * (y * x) ⋆
[xy]⋆x≈x[yx]⋆ x y = xy≈yz⇒x⋆y≈yz⋆ (*-assoc x y x)

-- Conway C12

[xy]⋆≈1+x[yx]⋆y : ∀ x y → (x * y) ⋆ ≈ 1# + x * (y * x) ⋆ * y
[xy]⋆≈1+x[yx]⋆y x y = begin-equality
  (x * y) ⋆                ≈⟨ x⋆≈1+x⋆x _ ⟩
  1# + (x * y) ⋆ * (x * y) ≈⟨ +-congˡ ([xy]⋆xy≈x[yx]⋆y _ _) ⟩
  1# + x * (y * x) ⋆ * y   ∎
  where
  [xy]⋆xy≈x[yx]⋆y : ∀ x y → (x * y) ⋆ * (x * y) ≈ x * (y * x) ⋆ * y
  [xy]⋆xy≈x[yx]⋆y x y = begin-equality
    (x * y) ⋆ * (x * y) ≈⟨ *-assoc _ _ _ ⟨
    (x * y) ⋆ * x * y   ≈⟨ *-congʳ $ [xy]⋆x≈x[yx]⋆ _ _ ⟩
    x * (y * x) ⋆ * y   ∎

-- Conway C11

module ConwayC11 x y where

  private
    LHS    = (x + y) ⋆
    x⋆y    = x ⋆ * y
    [x⋆y]⋆ = x⋆y ⋆
    RHS    = [x⋆y]⋆ * x ⋆
    1≤RHS : 1# ≤ RHS
    1≤RHS = begin
      1#       ≈⟨ *-identityˡ _ ⟨
      1# * 1#  ≤⟨ *-mono 1≤[ _ ]⋆ 1≤[ _ ]⋆ ⟩
      RHS      ∎
    x[x⋆y]≤x⋆y : x * x⋆y ≤ x⋆y
    x[x⋆y]≤x⋆y = begin
      x * x⋆y      ≈⟨ *-assoc _ _ _ ⟨
      x * x ⋆ * y  ≤⟨ *-monoʳ _ (xx⋆≤x⋆ _) ⟩
      x⋆y ∎
    x[x⋆y]⋆x⋆≤RHS : x * [x⋆y]⋆ * x ⋆ ≤ RHS
    x[x⋆y]⋆x⋆≤RHS = xy≤y∧xz≤z⇒xy⋆z≤y⋆z x[x⋆y]≤x⋆y (xx⋆≤x⋆ _)
    y[x⋆y]⋆x⋆≤RHS : y * [x⋆y]⋆ * x ⋆ ≤ RHS
    y[x⋆y]⋆x⋆≤RHS = begin
      y * [x⋆y]⋆ * x ⋆    ≤⟨ *-monoʳ _ $ *-monoʳ _ $ x≤y⋆x _ _ ⟩
      x⋆y * [x⋆y]⋆ * x ⋆  ≤⟨ *-monoʳ _ $ xx⋆≤x⋆ _ ⟩
      RHS                 ∎
    [x⋆y]LHS≤LHS : x⋆y * LHS ≤ LHS
    [x⋆y]LHS≤LHS = begin
     x⋆y * LHS        ≤⟨ *-monoʳ _ $ *-monoʳ _ $ ⋆-mono (x≤x+y _ _) ⟩
     (LHS * y) * LHS  ≤⟨ *-monoʳ _ $ *-monoˡ _ $ y≤x+y _ _ ⟩
     (LHS * _) * LHS  ≤⟨ *-monoʳ _ $ x⋆x≤x⋆ _ ⟩
     LHS * LHS        ≤⟨ x⋆x⋆≤x⋆ _ ⟩
     LHS ∎

  [x+y]⋆≤[x⋆y]⋆x⋆ : LHS ≤ RHS
  [x+y]⋆≤[x⋆y]⋆x⋆ = ⋆-elimˡ 1≤RHS $ begin
    (x + y) * RHS                       ≈⟨ *-assoc _ _ _ ⟨
    (x + y) * [x⋆y]⋆ * x ⋆              ≈⟨ *-congʳ $ distribʳ _ _ _ ⟩
    (x * [x⋆y]⋆ + y * [x⋆y]⋆) * x ⋆     ≈⟨ distribʳ _ _ _ ⟩
    x * [x⋆y]⋆ * x ⋆ + y * [x⋆y]⋆ * x ⋆ ≤⟨ x≤z∧y≤z⇒[x+y]≤z x[x⋆y]⋆x⋆≤RHS y[x⋆y]⋆x⋆≤RHS ⟩
    RHS                                 ∎
  [x⋆y]⋆x⋆≤[x+y]⋆ : RHS ≤ LHS
  [x⋆y]⋆x⋆≤[x+y]⋆ = begin
    RHS          ≤⟨ *-monoˡ _ $ ⋆-mono (x≤x+y _ _) ⟩
    [x⋆y]⋆ * LHS ≤⟨ ⋆-*-elimˡ $ [x⋆y]LHS≤LHS ⟩
    LHS          ∎

[x+y]⋆≈[x⋆y]⋆x⋆ : ∀ x y → (x + y) ⋆ ≈ (x ⋆ * y) ⋆ * x ⋆
[x+y]⋆≈[x⋆y]⋆x⋆ x y = ≤-antisym [x+y]⋆≤[x⋆y]⋆x⋆ [x⋆y]⋆x⋆≤[x+y]⋆
  where open ConwayC11 x y

