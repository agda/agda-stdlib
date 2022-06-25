------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of postulated Real numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.PostulatedReal.Properties where

open import Algebra.Construct.NaturalChoice.Base
import Algebra.Construct.NaturalChoice.MinMaxOp as MinMaxOp
import Algebra.Lattice.Construct.NaturalChoice.MinMaxOp as LatticeMinMaxOp
open import Data.PostulatedReal
open import Data.Sum
open import Function.Base
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

------------------------------------------------------------------------
-- Publicly re-export contents of core module and queries

open import Data.PostulatedReal.Properties.Core public

private
  variable
    x y : ℝ

------------------------------------------------------------------------
-- Properties of _⊓_
------------------------------------------------------------------------

x≤y⇒x⊔y≡y : x ≤ y → x ⊔ y ≡ y
x≤y⇒x⊔y≡y {x} {y} x≤y with x ≤? y
... | yes _   = refl
... | no  x≰y = contradiction x≤y x≰y

x≥y⇒x⊔y≡x : x ≥ y → x ⊔ y ≡ x
x≥y⇒x⊔y≡x {x} {y} x≥y with x ≤? y
... | yes x≤y = ≤-antisym x≥y x≤y
... | no  _   = refl

x≤y⇒x⊓y≡x : x ≤ y → x ⊓ y ≡ x
x≤y⇒x⊓y≡x {x} {y} x≤y with x ≤? y
... | yes _   = refl
... | no  x≰y = contradiction x≤y x≰y

x≥y⇒x⊓y≡y : x ≥ y → x ⊓ y ≡ y
x≥y⇒x⊓y≡y {x} {y} x≥y with x ≤? y
... | yes x≤y = ≤-antisym x≤y x≥y
... | no  _   = refl

⊓-operator : MinOperator ≤-totalPreorder
⊓-operator = record
  { x≤y⇒x⊓y≈x = x≤y⇒x⊓y≡x
  ; x≥y⇒x⊓y≈y = x≥y⇒x⊓y≡y
  }

⊔-operator : MaxOperator ≤-totalPreorder
⊔-operator = record
  { x≤y⇒x⊔y≈y = x≤y⇒x⊔y≡y
  ; x≥y⇒x⊔y≈x = x≥y⇒x⊔y≡x
  }

------------------------------------------------------------------------
-- Automatically derived properties of _⊓_ and _⊔_

private
  module ⊓-⊔-properties        = MinMaxOp        ⊓-operator ⊔-operator
  module ⊓-⊔-latticeProperties = LatticeMinMaxOp ⊓-operator ⊔-operator

open ⊓-⊔-properties public
  using
  ( ⊓-idem                    -- : Idempotent _⊓_
  ; ⊓-sel                     -- : Selective _⊓_
  ; ⊓-assoc                   -- : Associative _⊓_
  ; ⊓-comm                    -- : Commutative _⊓_

  ; ⊔-idem                    -- : Idempotent _⊔_
  ; ⊔-sel                     -- : Selective _⊔_
  ; ⊔-assoc                   -- : Associative _⊔_
  ; ⊔-comm                    -- : Commutative _⊔_

  ; ⊓-distribˡ-⊔              -- : _⊓_ DistributesOverˡ _⊔_
  ; ⊓-distribʳ-⊔              -- : _⊓_ DistributesOverʳ _⊔_
  ; ⊓-distrib-⊔               -- : _⊓_ DistributesOver  _⊔_
  ; ⊔-distribˡ-⊓              -- : _⊔_ DistributesOverˡ _⊓_
  ; ⊔-distribʳ-⊓              -- : _⊔_ DistributesOverʳ _⊓_
  ; ⊔-distrib-⊓               -- : _⊔_ DistributesOver  _⊓_
  ; ⊓-absorbs-⊔               -- : _⊓_ Absorbs _⊔_
  ; ⊔-absorbs-⊓               -- : _⊔_ Absorbs _⊓_
  ; ⊔-⊓-absorptive            -- : Absorptive _⊔_ _⊓_
  ; ⊓-⊔-absorptive            -- : Absorptive _⊓_ _⊔_

  ; ⊓-isMagma                 -- : IsMagma _⊓_
  ; ⊓-isSemigroup             -- : IsSemigroup _⊓_
  ; ⊓-isCommutativeSemigroup  -- : IsCommutativeSemigroup _⊓_
  ; ⊓-isBand                  -- : IsBand _⊓_
  ; ⊓-isSelectiveMagma        -- : IsSelectiveMagma _⊓_

  ; ⊔-isMagma                 -- : IsMagma _⊔_
  ; ⊔-isSemigroup             -- : IsSemigroup _⊔_
  ; ⊔-isCommutativeSemigroup  -- : IsCommutativeSemigroup _⊔_
  ; ⊔-isBand                  -- : IsBand _⊔_
  ; ⊔-isSelectiveMagma        -- : IsSelectiveMagma _⊔_

  ; ⊓-magma                   -- : Magma _ _
  ; ⊓-semigroup               -- : Semigroup _ _
  ; ⊓-band                    -- : Band _ _
  ; ⊓-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊓-selectiveMagma          -- : SelectiveMagma _ _

  ; ⊔-magma                   -- : Magma _ _
  ; ⊔-semigroup               -- : Semigroup _ _
  ; ⊔-band                    -- : Band _ _
  ; ⊔-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊔-selectiveMagma          -- : SelectiveMagma _ _

  ; ⊓-glb                     -- : ∀ {x y z} → x ≥ z → y ≥ z → x ⊓ y ≥ z
  ; ⊓-triangulate             -- : ∀ x y z → x ⊓ y ⊓ z ≡ (x ⊓ y) ⊓ (y ⊓ z)
  ; ⊓-mono-≤                  -- : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ; ⊓-monoˡ-≤                 -- : ∀ x → (_⊓ x) Preserves _≤_ ⟶ _≤_
  ; ⊓-monoʳ-≤                 -- : ∀ x → (x ⊓_) Preserves _≤_ ⟶ _≤_

  ; ⊔-lub                     -- : ∀ {x y z} → x ≤ z → y ≤ z → x ⊔ y ≤ z
  ; ⊔-triangulate             -- : ∀ x y z → x ⊔ y ⊔ z ≡ (x ⊔ y) ⊔ (y ⊔ z)
  ; ⊔-mono-≤                  -- : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ; ⊔-monoˡ-≤                 -- : ∀ x → (_⊔ x) Preserves _≤_ ⟶ _≤_
  ; ⊔-monoʳ-≤                 -- : ∀ x → (x ⊔_) Preserves _≤_ ⟶ _≤_
  )
  renaming
  ( x⊓y≈y⇒y≤x to x⊓y≡y⇒y≤x    -- : ∀ {x y} → x ⊓ y ≡ y → y ≤ x
  ; x⊓y≈x⇒x≤y to x⊓y≡x⇒x≤y    -- : ∀ {x y} → x ⊓ y ≡ x → x ≤ y
  ; x⊓y≤x     to x⊓y≤x        -- : ∀ x y → x ⊓ y ≤ x
  ; x⊓y≤y     to x⊓y≤y        -- : ∀ x y → x ⊓ y ≤ y
  ; x≤y⇒x⊓z≤y to x≤y⇒x⊓r≤y    -- : ∀ {x y} r → x ≤ y → x ⊓ r ≤ y
  ; x≤y⇒z⊓x≤y to x≤y⇒r⊓x≤y    -- : ∀ {x y} r → x ≤ y → r ⊓ x ≤ y
  ; x≤y⊓z⇒x≤y to x≤y⊓r⇒x≤y    -- : ∀ {x} y r → x ≤ y ⊓ r → x ≤ y
  ; x≤y⊓z⇒x≤z to x≤y⊓r⇒x≤r    -- : ∀ {x} y r → x ≤ y ⊓ r → x ≤ r

  ; x⊔y≈y⇒x≤y to x⊔y≡y⇒x≤y    -- : ∀ {x y} → x ⊔ y ≡ y → x ≤ y
  ; x⊔y≈x⇒y≤x to x⊔y≡x⇒y≤x    -- : ∀ {x y} → x ⊔ y ≡ x → y ≤ x
  ; x≤x⊔y     to x≤x⊔y        -- : ∀ x y → x ≤ x ⊔ y
  ; x≤y⊔x     to x≤y⊔x        -- : ∀ x y → x ≤ y ⊔ x
  ; x≤y⇒x≤y⊔z to x≤y⇒x≤y⊔r    -- : ∀ {x y} z → x ≤ y → x ≤ y ⊔ z
  ; x≤y⇒x≤z⊔y to x≤y⇒x≤r⊔y    -- : ∀ {x y} z → x ≤ y → x ≤ z ⊔ y
  ; x⊔y≤z⇒x≤z to x⊔y≤r⇒x≤r    -- : ∀ x y {z} → x ⊔ y ≤ z → x ≤ z
  ; x⊔y≤z⇒y≤z to x⊔y≤r⇒y≤r    -- : ∀ x y {z} → x ⊔ y ≤ z → y ≤ z

  ; x⊓y≤x⊔y   to x⊓y≤x⊔y      -- : ∀ x y → x ⊓ y ≤ x ⊔ y
  )

open ⊓-⊔-latticeProperties public
  using
  ( ⊓-isSemilattice           -- : IsSemilattice _⊓_
  ; ⊔-isSemilattice           -- : IsSemilattice _⊔_
  ; ⊔-⊓-isLattice             -- : IsLattice _⊔_ _⊓_
  ; ⊓-⊔-isLattice             -- : IsLattice _⊓_ _⊔_
  ; ⊔-⊓-isDistributiveLattice -- : IsDistributiveLattice _⊔_ _⊓_
  ; ⊓-⊔-isDistributiveLattice -- : IsDistributiveLattice _⊓_ _⊔_

  ; ⊓-semilattice             -- : Semilattice _ _
  ; ⊔-semilattice             -- : Semilattice _ _
  ; ⊔-⊓-lattice               -- : Lattice _ _
  ; ⊓-⊔-lattice               -- : Lattice _ _
  ; ⊔-⊓-distributiveLattice   -- : DistributiveLattice _ _
  ; ⊓-⊔-distributiveLattice   -- : DistributiveLattice _ _
  )

------------------------------------------------------------------------
-- Other properties of _⊓_ and _⊔_

mono-≤-distrib-⊔ : ∀ {f} → f Preserves _≤_ ⟶ _≤_ →
                   ∀ x y → f (x ⊔ y) ≡ f x ⊔ f y
mono-≤-distrib-⊔ {f} = ⊓-⊔-properties.mono-≤-distrib-⊔ (cong f)

mono-≤-distrib-⊓ : ∀ {f} → f Preserves _≤_ ⟶ _≤_ →
                   ∀ x y → f (x ⊓ y) ≡ f x ⊓ f y
mono-≤-distrib-⊓ {f} = ⊓-⊔-properties.mono-≤-distrib-⊓ (cong f)

mono-<-distrib-⊓ : ∀ {f} → f Preserves _<_ ⟶ _<_ →
                   ∀ x y → f (x ⊓ y) ≡ f x ⊓ f y
mono-<-distrib-⊓ {f} f-mono-< x y with <-cmp x y
... | tri< x<y x≢z  x≯y = begin
  f (x ⊓ y)  ≡⟨ cong f (x≤y⇒x⊓y≡x (<⇒≤ x<y)) ⟩
  f x        ≡˘⟨ x≤y⇒x⊓y≡x (<⇒≤ (f-mono-< x<y)) ⟩
  f x ⊓ f y  ∎
  where open ≡-Reasoning
... | tri≈ x≮y refl x≯y = begin
  f (x ⊓ y)  ≡⟨ cong f (⊓-idem x) ⟩
  f x        ≡˘⟨ ⊓-idem (f x) ⟩
  f x ⊓ f y  ∎
  where open ≡-Reasoning
... | tri> z≮y x≡z  x>y = begin
  f (x ⊓ y)  ≡⟨ cong f (x≥y⇒x⊓y≡y (<⇒≤ x>y)) ⟩
  f y        ≡˘⟨ x≥y⇒x⊓y≡y (<⇒≤ (f-mono-< x>y)) ⟩
  f x ⊓ f y  ∎
  where open ≡-Reasoning

mono-<-distrib-⊔ : ∀ {f} → f Preserves _<_ ⟶ _<_ →
                   ∀ x y → f (x ⊔ y) ≡ f x ⊔ f y
mono-<-distrib-⊔ {f} f-mono-< x y with <-cmp x y
... | tri< x<y x≢z  x≯y = begin
  f (x ⊔ y)  ≡⟨ cong f (x≤y⇒x⊔y≡y (<⇒≤ x<y)) ⟩
  f y        ≡˘⟨ x≤y⇒x⊔y≡y (<⇒≤ (f-mono-< x<y)) ⟩
  f x ⊔ f y  ∎
  where open ≡-Reasoning
... | tri≈ x≮y refl x≯y = begin
  f (x ⊔ y)  ≡⟨ cong f (⊔-idem x) ⟩
  f y        ≡˘⟨ ⊔-idem (f x) ⟩
  f x ⊔ f y  ∎
  where open ≡-Reasoning
... | tri> x≮y x≡z  x>y = begin
  f (x ⊔ y)  ≡⟨ cong f (x≥y⇒x⊔y≡x (<⇒≤ x>y)) ⟩
  f x        ≡˘⟨ x≥y⇒x⊔y≡x (<⇒≤ (f-mono-< x>y)) ⟩
  f x ⊔ f y  ∎
  where open ≡-Reasoning

antimono-≤-distrib-⊓ : ∀ {f} → f Preserves _≤_ ⟶ _≥_ →
                       ∀ x y → f (x ⊓ y) ≡ f x ⊔ f y
antimono-≤-distrib-⊓ {f} = ⊓-⊔-properties.antimono-≤-distrib-⊓ (cong f)

antimono-≤-distrib-⊔ : ∀ {f} → f Preserves _≤_ ⟶ _≥_ →
                       ∀ x y → f (x ⊔ y) ≡ f x ⊓ f y
antimono-≤-distrib-⊔ {f} = ⊓-⊔-properties.antimono-≤-distrib-⊔ (cong f)

------------------------------------------------------------------------
-- Properties of _⊓_ and _*_

*-distribˡ-⊓-nonNeg : ∀ x .{{_ : NonNegative x}} → ∀ y z → x * (y ⊓ z) ≡ (x * y) ⊓ (x * z)
*-distribˡ-⊓-nonNeg x = mono-≤-distrib-⊓ (*-monoˡ-≤-nonNeg x)

*-distribʳ-⊓-nonNeg : ∀ x .{{_ : NonNegative x}} → ∀ y z → (y ⊓ z) * x ≡ (y * x) ⊓ (z * x)
*-distribʳ-⊓-nonNeg x = mono-≤-distrib-⊓ (*-monoʳ-≤-nonNeg x)

*-distribˡ-⊔-nonNeg : ∀ x .{{_ : NonNegative x}} → ∀ y z → x * (y ⊔ z) ≡ (x * y) ⊔ (x * z)
*-distribˡ-⊔-nonNeg x = mono-≤-distrib-⊔ (*-monoˡ-≤-nonNeg x)

*-distribʳ-⊔-nonNeg : ∀ x .{{_ : NonNegative x}} → ∀ y z → (y ⊔ z) * x ≡ (y * x) ⊔ (z * x)
*-distribʳ-⊔-nonNeg x = mono-≤-distrib-⊔ (*-monoʳ-≤-nonNeg x)

------------------------------------------------------------------------
-- Properties of _⊓_, _⊔_ and _*_

*-distribˡ-⊔-nonPos : ∀ x .{{_ : NonPositive x}} → ∀ y z → x * (y ⊔ z) ≡ (x * y) ⊓ (x * z)
*-distribˡ-⊔-nonPos x = antimono-≤-distrib-⊔ (*-monoˡ-≤-nonPos x)

*-distribʳ-⊔-nonPos : ∀ x .{{_ : NonPositive x}} → ∀ y z → (y ⊔ z) * x ≡ (y * x) ⊓ (z * x)
*-distribʳ-⊔-nonPos x = antimono-≤-distrib-⊔ (*-monoʳ-≤-nonPos x)

*-distribˡ-⊓-nonPos : ∀ x .{{_ : NonPositive x}} → ∀ y z → x * (y ⊓ z) ≡ (x * y) ⊔ (x * z)
*-distribˡ-⊓-nonPos x = antimono-≤-distrib-⊓ (*-monoˡ-≤-nonPos x)

*-distribʳ-⊓-nonPos : ∀ x .{{_ : NonPositive x}} → ∀ y z → (y ⊓ z) * x ≡ (y * x) ⊔ (z * x)
*-distribʳ-⊓-nonPos x = antimono-≤-distrib-⊓ (*-monoʳ-≤-nonPos x)

------------------------------------------------------------------------
-- Properties of ∣_∣
------------------------------------------------------------------------

∣x∣≡0⇒x≡0 : ∀ x → ∣ x ∣ ≡ 0ℝ → x ≡ 0ℝ
∣x∣≡0⇒x≡0 x ∣x∣≡0 with 0ℝ ≤? x
... | yes _ = ∣x∣≡0
... | no  _ = -x≡0⇒x≡0 ∣x∣≡0

0≤∣x∣ : ∀ x → 0ℝ ≤ ∣ x ∣
0≤∣x∣ x with 0ℝ ≤? x
... | yes x≥0 = x≥0
... | no  x≱0 with ≰⇒> x≱0
... | *<* x≤0 _ = begin
  0ℝ   ≡˘⟨ -0#≈0# ⟩
  - 0ℝ ≤⟨ neg-antimono-≤ x≤0 ⟩
  - x  ∎
  where open ≤-Reasoning

0≤x⇒∣x∣≡x : 0ℝ ≤ x → ∣ x ∣ ≡ x
0≤x⇒∣x∣≡x {x} 0≤x with 0ℝ ≤? x
... | yes _   = refl
... | no  x≱0 = contradiction 0≤x x≱0

∣-x∣≡∣x∣ : ∀ x → ∣ - x ∣ ≡ ∣ x ∣
∣-x∣≡∣x∣ x  with 0ℝ ≤? x | 0ℝ ≤? - x
... | yes _ | no  _ = -‿involutive x
... | no  _ | yes _ = refl
... | yes x≥0 | yes -x≥0 rewrite x≥0∧-x≥0⇒x≡0 x≥0 -x≥0 = -0#≈0#
... | no  x≱0 | no  -x≱0 with <⇒≤ $ ≰⇒> x≱0 | <⇒≤ $ ≰⇒> -x≱0
... | x≤0 | -x≤0 rewrite x≤0∧-x≤0⇒x≡0 x≤0 -x≤0 = cong (-_) -0#≈0#

∣x∣≡x⇒0≤x : ∀ {x} → ∣ x ∣ ≡ x → 0ℝ ≤ x
∣x∣≡x⇒0≤x {x} ∣x∣≡x with 0ℝ ≤? x
... | yes x≥0 = x≥0
... | no  x≱0 with ≰⇒> x≱0
... | *<* _ x≢0 = contradiction (-x≡x⇒x≡0 ∣x∣≡x) x≢0

∣x∣≡x∨∣x∣≡-x : ∀ x → ∣ x ∣ ≡ x ⊎ ∣ x ∣ ≡ - x
∣x∣≡x∨∣x∣≡-x x with  0ℝ ≤? x
... | yes x≥0 = inj₁ refl
... | no  x≱0 = inj₂ refl

∣x+y∣≤∣x∣+∣y∣ : ∀ x y → ∣ x + y ∣ ≤ ∣ x ∣ + ∣ y ∣
∣x+y∣≤∣x∣+∣y∣ x y with 0ℝ ≤? x | 0ℝ ≤? y | 0ℝ ≤? x + y
... | yes x≥0 | yes y≥0 | yes x+y≥0 = ≤-refl
... | yes x≥0 | yes y≥0 | no  x+y≱0 = contradiction
  (≤-trans (≤-reflexive $ sym $ +-identityˡ 0ℝ) (+-mono-≤ x≥0 y≥0)) x+y≱0
... | yes x≥0 | no  y≱0 | yes x+y≥0 = let
  y≤0 = <⇒≤ $ ≰⇒> y≱0
  in +-monoʳ-≤ x (x≤0⇒-x≥x y≤0)
... | yes x≥0 | no  y≱0 | no  x+y≱0 rewrite sym $ -‿+-comm x y =
  +-monoˡ-≤ (- y) (x≥0⇒-x≤x x≥0)
... | no  x≱0 | yes y≥0 | yes x+y≥0 = let
  x≤0 = <⇒≤ $ ≰⇒> x≱0
  in +-monoˡ-≤ y (x≤0⇒-x≥x x≤0)
... | no  x≱0 | yes y≥0 | no  x+y≱0 rewrite sym $ -‿+-comm x y =
  +-monoʳ-≤ (- x) (x≥0⇒-x≤x y≥0)
... | no  x≱0 | no  y≱0 | yes x+y≥0 rewrite -‿+-comm x y | (let
  x≤0 = <⇒≤ $ ≰⇒> x≱0
  y≤0 = <⇒≤ $ ≰⇒> y≱0
  x+y≤0 = (≤-trans (+-mono-≤ x≤0 y≤0) (≤-reflexive $ +-identityˡ 0ℝ))
  in ≤-antisym x+y≤0 x+y≥0) | -0#≈0# = ≤-refl
... | no  x≱0 | no  y≱0 | no  x+y≱0 rewrite sym $ -‿+-comm x y = ≤-refl

∣x-y∣≤∣x∣+∣y∣ : ∀ x y → ∣ x - y ∣ ≤ ∣ x ∣ + ∣ y ∣
∣x-y∣≤∣x∣+∣y∣ x y = begin
  ∣ x - y ∣       ≤⟨ ∣x+y∣≤∣x∣+∣y∣ x (- y) ⟩
  ∣ x ∣ + ∣ - y ∣ ≡⟨ (cong (∣ x ∣ +_) $ ∣-x∣≡∣x∣ y) ⟩
  ∣ x ∣ + ∣ y ∣   ∎
  where open ≤-Reasoning

∣x*y∣≡∣x∣*∣y∣ : ∀ x y → ∣ x * y ∣ ≡ ∣ x ∣ * ∣ y ∣
∣x*y∣≡∣x∣*∣y∣ x y with 0ℝ ≤? x | 0ℝ ≤? y | 0ℝ ≤? x * y
... | yes x≥0 | yes y≥0 | yes xy≥0 = refl
... | yes x≥0 | yes y≥0 | no  xy≱0 = contradiction (*-mono-≥0 x≥0 y≥0) xy≱0
... | yes x≥0 | no  y≱0 | yes xy≥0 rewrite sym $ -‿distribʳ-* x y | let
  y≤0 = <⇒≤ $ ≰⇒> y≱0
  in ≤-antisym (*-mono-≥0-≤0 x≥0 y≤0) xy≥0 = sym $ -0#≈0#
... | yes x≥0 | no  y≱0 | no  xy≱0 = -‿distribʳ-* x y
... | no  x≱0 | yes y≥0 | yes xy≥0 rewrite sym $ -‿distribˡ-* x y | let
  x≤0 = <⇒≤ $ ≰⇒> x≱0
  in ≤-antisym (*-mono-≤0-≥0 x≤0 y≥0) xy≥0 = sym $ -0#≈0#
... | no  x≱0 | yes y≥0 | no  xy≱0 = -‿distribˡ-* x y
... | no  x≱0 | no  y≱0 | yes xy≥0 = sym $ *-cancel-neg x y
... | no  x≱0 | no  y≱0 | no  xy≱0 = let
  x≤0 = <⇒≤ $ ≰⇒> x≱0
  y≤0 = <⇒≤ $ ≰⇒> y≱0
  in contradiction (*-mono-≤0 x≤0 y≤0) xy≱0

∣x*x∣≡x*x : ∀ x → ∣ x ∣ * ∣ x ∣ ≡ x * x
∣x*x∣≡x*x x with 0ℝ ≤? x
... | yes x≥0 = refl
... | no  x≱0 = *-cancel-neg x x

∣-∣-nonNeg : ∀ x → NonNegative ∣ x ∣
∣-∣-nonNeg x = nonNegative $ 0≤∣x∣ x

∣∣x∣∣≡∣x∣ : ∀ x → ∣ ∣ x ∣ ∣ ≡ ∣ x ∣
∣∣x∣∣≡∣x∣ x = 0≤x⇒∣x∣≡x $ 0≤∣x∣ x

