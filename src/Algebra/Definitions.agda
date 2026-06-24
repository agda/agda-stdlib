------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`, unless
-- you want to parameterise it via the equality relation.

-- Note that very few of the element arguments are made implicit here,
-- as we do not assume that the Agda can infer either the right or left
-- argument of the binary operators. This is despite the fact that the
-- library defines most of its concrete operators (e.g. in
-- `Data.Nat.Base`) as being left-biased.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)

module Algebra.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where

open import Algebra.Core using (Op₁; Op₂)
open import Data.Product.Base using (_×_; ∃-syntax)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Definitions as Definitions
  using (Monotonic₁; Monotonic₂)
open import Relation.Nullary.Negation.Core using (¬_)


------------------------------------------------------------------------
-- Properties of operations

Congruent₁ : Op₁ A → Set _
Congruent₁ = Monotonic₁ _≈_ _≈_

Congruent₂ : Op₂ A → Set _
Congruent₂ = Monotonic₂ _≈_ _≈_ _≈_

LeftCongruent : Op₂ A → Set _
LeftCongruent _∙_ = ∀ {x} → Congruent₁ (x ∙_)

RightCongruent : Op₂ A → Set _
RightCongruent _∙_ = ∀ {x} → Congruent₁ (_∙ x)

Associative : Op₂ A → Set _
Associative _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

Commutative : Op₂ A → Set _
Commutative _∙_ = ∀ x y → (x ∙ y) ≈ (y ∙ x)

-- An element is called `Central` for a binary operation
-- if it commutes with all other elements.
Central : Op₂ A → A → Set _
Central _∙_ x = ∀ y → (x ∙ y) ≈ (y ∙ x)

LeftIdentity : A → Op₂ A → Set _
LeftIdentity e _∙_ = ∀ x → (e ∙ x) ≈ x

RightIdentity : A → Op₂ A → Set _
RightIdentity e _∙_ = ∀ x → (x ∙ e) ≈ x

Identity : A → Op₂ A → Set _
Identity e ∙ = (LeftIdentity e ∙) × (RightIdentity e ∙)

LeftZero : A → Op₂ A → Set _
LeftZero z _∙_ = ∀ x → (z ∙ x) ≈ z

RightZero : A → Op₂ A → Set _
RightZero z _∙_ = ∀ x → (x ∙ z) ≈ z

Zero : A → Op₂ A → Set _
Zero z ∙ = (LeftZero z ∙) × (RightZero z ∙)

LeftInverse : A → Op₁ A → Op₂ A → Set _
LeftInverse e _⁻¹ _∙_ = ∀ x → ((x ⁻¹) ∙ x) ≈ e

RightInverse : A → Op₁ A → Op₂ A → Set _
RightInverse e _⁻¹ _∙_ = ∀ x → (x ∙ (x ⁻¹)) ≈ e

Inverse : A → Op₁ A → Op₂ A → Set _
Inverse e ⁻¹ ∙ = (LeftInverse e ⁻¹) ∙ × (RightInverse e ⁻¹ ∙)

-- For structures in which not every element has an inverse (e.g. Fields)
LeftInvertible : A → Op₂ A → A → Set _
LeftInvertible e _∙_ x = ∃[ x⁻¹ ] (x⁻¹ ∙ x) ≈ e

RightInvertible : A → Op₂ A → A → Set _
RightInvertible e _∙_ x = ∃[ x⁻¹ ] (x ∙ x⁻¹) ≈ e

-- NB: this is not quite the same as
-- LeftInvertible e ∙ x × RightInvertible e ∙ x
-- since the left and right inverses have to coincide.
Invertible : A → Op₂ A → A → Set _
Invertible e _∙_ x = ∃[ x⁻¹ ] (x⁻¹ ∙ x) ≈ e × (x ∙ x⁻¹) ≈ e

LeftConical : A → Op₂ A → Set _
LeftConical e _∙_ = ∀ x y → (x ∙ y) ≈ e → x ≈ e

RightConical : A → Op₂ A → Set _
RightConical e _∙_ = ∀ x y → (x ∙ y) ≈ e → y ≈ e

Conical : A → Op₂ A → Set _
Conical e ∙ = (LeftConical e ∙) × (RightConical e ∙)

infix 4 _DistributesOverˡ_ _DistributesOverʳ_ _DistributesOver_

_DistributesOverˡ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverˡ _+_ =
  ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))

_DistributesOverʳ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverʳ _+_ =
  ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))

_DistributesOver_ : Op₂ A → Op₂ A → Set _
* DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)

infix 4 _MiddleFourExchange_ _IdempotentOn_ _Absorbs_

_MiddleFourExchange_ : Op₂ A → Op₂ A → Set _
_*_ MiddleFourExchange _+_ =
  ∀ w x y z → ((w + x) * (y + z)) ≈ ((w + y) * (x + z))

_IdempotentOn_ : Op₂ A → A → Set _
_∙_ IdempotentOn x = (x ∙ x) ≈ x

Idempotent : Op₂ A → Set _
Idempotent ∙ = ∀ x → ∙ IdempotentOn x

IdempotentFun : Op₁ A → Set _
IdempotentFun f = ∀ x → f (f x) ≈ f x

Selective : Op₂ A → Set _
Selective _∙_ = ∀ x y → (x ∙ y) ≈ x ⊎ (x ∙ y) ≈ y

_Absorbs_ : Op₂ A → Op₂ A → Set _
_∙_ Absorbs _∘_ = ∀ x y → (x ∙ (x ∘ y)) ≈ x

Absorptive : Op₂ A → Op₂ A → Set _
Absorptive ∙ ∘ = (∙ Absorbs ∘) × (∘ Absorbs ∙)

SelfInverse : Op₁ A → Set _
SelfInverse f = ∀ {x y} → f x ≈ y → f y ≈ x

Involutive : Op₁ A → Set _
Involutive f = ∀ x → f (f x) ≈ x

LeftCancellative : Op₂ A → Set _
LeftCancellative _•_ = ∀ x y z → (x • y) ≈ (x • z) → y ≈ z

RightCancellative : Op₂ A → Set _
RightCancellative _•_ = ∀ x y z → (y • x) ≈ (z • x) → y ≈ z

Cancellative : Op₂ A → Set _
Cancellative _•_ = (LeftCancellative _•_) × (RightCancellative _•_)

AlmostLeftCancellative : A → Op₂ A → Set _
AlmostLeftCancellative e _•_ = ∀ x y z → ¬ x ≈ e → (x • y) ≈ (x • z) → y ≈ z

AlmostRightCancellative : A → Op₂ A → Set _
AlmostRightCancellative e _•_ = ∀ x y z → ¬ x ≈ e → (y • x) ≈ (z • x) → y ≈ z

AlmostCancellative : A → Op₂ A → Set _
AlmostCancellative e _•_ = AlmostLeftCancellative e _•_ × AlmostRightCancellative e _•_

Interchangable : Op₂ A → Op₂ A → Set _
Interchangable _∘_ _∙_ = ∀ w x y z → ((w ∙ x) ∘ (y ∙ z)) ≈ ((w ∘ y) ∙ (x ∘ z))

LeftDividesˡ : Op₂ A → Op₂ A → Set _
LeftDividesˡ _∙_  _\\_ = ∀ x y → (x ∙ (x \\ y)) ≈ y

LeftDividesʳ : Op₂ A → Op₂ A → Set _
LeftDividesʳ _∙_ _\\_ = ∀ x y → (x \\ (x ∙ y)) ≈ y

RightDividesˡ : Op₂ A → Op₂ A → Set _
RightDividesˡ _∙_ _//_ = ∀ x y → ((y // x) ∙ x) ≈ y

RightDividesʳ : Op₂ A → Op₂ A → Set _
RightDividesʳ _∙_ _//_ = ∀ x y → ((y ∙ x) // x) ≈ y

LeftDivides : Op₂ A → Op₂ A → Set _
LeftDivides ∙ \\ = (LeftDividesˡ ∙ \\) × (LeftDividesʳ ∙ \\)

RightDivides : Op₂ A → Op₂ A → Set _
RightDivides ∙ // = (RightDividesˡ ∙ //) × (RightDividesʳ ∙ //)

LeftAlternative : Op₂ A → Set _
LeftAlternative _∙_ = ∀ x y  →  ((x ∙ x) ∙ y) ≈ (x ∙ (x ∙ y))

RightAlternative : Op₂ A → Set _
RightAlternative _∙_ = ∀ x y → (x ∙ (y ∙ y)) ≈ ((x ∙ y) ∙ y)

Alternative : Op₂ A → Set _
Alternative _∙_ = (LeftAlternative _∙_ ) × (RightAlternative _∙_)

Flexible : Op₂ A → Set _
Flexible _∙_ = ∀ x y → ((x ∙ y) ∙ x) ≈ (x ∙ (y ∙ x))

Medial : Op₂ A → Set _
Medial _∙_ = Interchangable _∙_ _∙_

LeftSemimedial : Op₂ A → Set _
LeftSemimedial _∙_ = ∀ x y z → ((x ∙ x) ∙ (y ∙ z)) ≈ ((x ∙ y) ∙ (x ∙ z))

RightSemimedial : Op₂ A → Set _
RightSemimedial _∙_ = ∀ x y z → ((y ∙ z) ∙ (x ∙ x)) ≈ ((y ∙ x) ∙ (z ∙ x))

Semimedial : Op₂ A → Set _
Semimedial _∙_ = (LeftSemimedial _∙_) × (RightSemimedial _∙_)

LeftBol : Op₂ A → Set _
LeftBol _∙_ = ∀ x y z → (x ∙ (y ∙ (x ∙ z))) ≈ ((x ∙ (y ∙ x)) ∙ z )

RightBol : Op₂ A → Set _
RightBol _∙_ = ∀ x y z → (((z ∙ x) ∙ y) ∙ x) ≈ (z ∙ ((x ∙ y) ∙ x))

MiddleBol : Op₂ A → Op₂ A  → Op₂ A  → Set _
MiddleBol _∙_ _\\_ _//_ = ∀ x y z → (x ∙ ((y ∙ z) \\ x)) ≈ ((x // z) ∙ (y \\ x))

Identical : Op₂ A → Set _
Identical _∙_ = ∀ x y z → ((z ∙ x) ∙ (y ∙ z)) ≈ (z ∙ ((x ∙ y) ∙ z))


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 3.0

module _ (e : A) (_+_ _*_ : Op₂ A) (_⋆ : Op₁ A) where
  StarLeftExpansive = Definitions.StarLeftExpansive _≈_ e _+_ _*_ _⋆
  {-# WARNING_ON_USAGE StarLeftExpansive
  "Warning: StarLeftExpansive was deprecated in v3.0.
  Please use Relation.Binary.Definitions.StarLeftExpansive instead."
  #-}
  StarRightExpansive = Definitions.StarRightExpansive _≈_ e _+_ _*_ _⋆
  {-# WARNING_ON_USAGE StarRightExpansive
  "Warning: StarRightExpansive was deprecated in v3.0.
  Please use Relation.Binary.Definitions.StarRightExpansive instead."
  #-}
  StarExpansive = Definitions.StarExpansive _≈_ e _+_ _*_ _⋆
  {-# WARNING_ON_USAGE StarExpansive
  "Warning: StarExpansive was deprecated in v3.0.
  Please use Relation.Binary.Definitions.StarExpansive instead."
  #-}
module _ (_+_ _*_ : Op₂ A) (_⋆ : Op₁ A) where
  StarLeftDestructive = Definitions.StarLeftDestructive _≈_ _+_ _*_ _⋆
  {-# WARNING_ON_USAGE StarLeftDestructive
  "Warning: StarLeftDestructive was deprecated in v3.0.
  Please use Relation.Binary.Definitions.StarLeftDestructive instead."
  #-}
  StarRightDestructive = Definitions.StarRightDestructive _≈_ _+_ _*_ _⋆
  {-# WARNING_ON_USAGE StarRightDestructive
  "Warning: StarRightDestructive was deprecated in v3.0.
  Please use Relation.Binary.Definitions.StarRightDestructive instead."
  #-}
  StarDestructive = Definitions.StarDestructive _≈_ _+_ _*_ _⋆
  {-# WARNING_ON_USAGE StarDestructive
  "Warning: StarDestructive was deprecated in v3.0.
  Please use Relation.Binary.Definitions.StarDestructive instead."
  #-}
