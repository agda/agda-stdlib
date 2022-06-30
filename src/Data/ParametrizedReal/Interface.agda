------------------------------------------------------------------------
-- The Agda standard library
--
-- Interface for parametrized Real numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.ParametrizedReal.Interface where

open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary using (¬_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; ≢-sym)

record RealsCore : Set₁ where
  field
    ℝ     : Set
    0ℝ 1ℝ : ℝ
    1≢0   : 1ℝ ≢ 0ℝ

    _≤_ : Rel ℝ 0ℓ
    0≤1 : 0ℝ ≤ 1ℝ

  ----------------------------------------------------------------------
  -- Ordering of reals

  infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≱_ _≮_ _≯_

  data _<_ : Rel ℝ 0ℓ where
    *<* : ∀ {x y} → x ≤ y → x ≢ y → x < y

  _≥_ : Rel ℝ 0ℓ
  x ≥ y = y ≤ x

  _>_ : Rel ℝ 0ℓ
  x > y = y < x

  _≰_ : Rel ℝ 0ℓ
  x ≰ y = ¬ (x ≤ y)

  _≱_ : Rel ℝ 0ℓ
  x ≱ y = ¬ (x ≥ y)

  _≮_ : Rel ℝ 0ℓ
  x ≮ y = ¬ (x < y)

  _≯_ : Rel ℝ 0ℓ
  x ≯ y = ¬ (x > y)

  ----------------------------------------------------------------------
  -- Simple predicates

  record NonZero (x : ℝ) : Set where
    field nonZero : x ≢ 0ℝ

  record Positive (x : ℝ) : Set where
    field positive : x > 0ℝ

  record Negative (x : ℝ) : Set where
    field negative : x < 0ℝ

  record NonPositive (x : ℝ) : Set where
    field nonPositive : x ≤ 0ℝ

  record NonNegative (x : ℝ) : Set where
    field nonNegative : x ≥ 0ℝ


module _ (Core : RealsCore) where
  open RealsCore Core
  open import Algebra.Definitions {A = ℝ} _≡_

  record RealsOps : Set where
    infix  8 -_ 1/_
    infixl 7 _*_ _/_
    infixl 6 _-_ _+_
    infix 4 _≟_

    field
      _+_ : ℝ → ℝ → ℝ
      -_  : ℝ → ℝ
      _*_ : ℝ → ℝ → ℝ
      1/_ : (x : ℝ) .⦃ _ : NonZero x ⦄ → ℝ

      +-assoc     : Associative _+_
      +-comm      : Commutative _+_
      +-identityˡ : LeftIdentity 0ℝ _+_
      +-inverseˡ  : LeftInverse 0ℝ -_ _+_

      *-assoc         : Associative _*_
      *-comm          : Commutative _*_
      *-identityˡ     : LeftIdentity 1ℝ _*_
      *-distribˡ-+    : _*_ DistributesOverˡ _+_
      *-neg-identityˡ : (x : ℝ) → (- 1ℝ) * x ≡ - x
      *-inverseˡ      : ∀ x .⦃ _ : NonZero x  ⦄ → (1/ x) * x ≡ 1ℝ

      _≟_ : DecidableEquality ℝ

      ≤-refl    : Reflexive _≤_
      ≤-antisym : Antisymmetric _≡_ _≤_
      ≤-trans   : Transitive _≤_
      ≤-total   : Total _≤_

      +-mono-≤         : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
      *-monoʳ-≤-nonNeg : ∀ z .⦃ _ : NonNegative z ⦄ → (_* z) Preserves _≤_ ⟶ _≤_


record Reals : Set₁ where
  field
    core : RealsCore
    ops  : RealsOps core

  open RealsCore core public
  open RealsOps ops public

