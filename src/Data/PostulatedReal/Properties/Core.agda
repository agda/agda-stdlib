------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties of Real numbers
------------------------------------------------------------------------


{-# OPTIONS --without-K #-}

module Data.PostulatedReal.Properties.Core where

open import Function.Base using (_$_)
open import Data.PostulatedReal.Base
open import Data.Sum.Base
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

private
  variable
    x y z : ℝ

------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

infix 4 _≟_

postulate
  _≟_ : DecidableEquality ℝ

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid ℝ

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≟_

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Relational properties

postulate
  ≤-refl    : Reflexive _≤_
  ≤-antisym : Antisymmetric _≡_ _≤_
  ≤-trans   : Transitive _≤_
  ≤-total   : Total _≤_

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive refl = ≤-refl

------------------------------------------------------------------------
-- Structures

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isTotalPreorder : IsTotalPreorder _≡_ _≤_
≤-isTotalPreorder = record
  { isPreorder = ≤-isPreorder
  ; total      = ≤-total
  }

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isTotalOrder : IsTotalOrder _≡_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

------------------------------------------------------------------------
-- Bundles

≤-totalPreorder : TotalPreorder 0ℓ 0ℓ 0ℓ
≤-totalPreorder = record
  { isTotalPreorder = ≤-isTotalPreorder
  }

------------------------------------------------------------------------
-- Properties of _<_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Relational properties

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (*<* x≤y _) = x≤y

≮⇒≥ : _≮_ ⇒ _≥_
≮⇒≥ {x} {y} x≮y with ≤-total x y
... | inj₁ x≤y with x ≟ y
... | yes x≡y = ≤-reflexive $ sym x≡y
... | no  x≢y = contradiction (*<* x≤y x≢y) x≮y
≮⇒≥ x≮y | inj₂ x≥y = x≥y

≰⇒> : _≰_ ⇒ _>_
≰⇒> {x} {y} x≰y  with ≤-total x y
... | inj₁ x≤y = contradiction x≤y x≰y
... | inj₂ x≥y  with x ≟ y
... | yes x≡y = contradiction (≤-reflexive x≡y) x≰y
... | no  x≢y = *<* x≥y (≢-sym x≢y)
<⇒≢ : _<_ ⇒ _≢_
<⇒≢ (*<* _ x≢y) = x≢y

<-irrefl : Irreflexive _≡_ _<_
<-irrefl x≡x (*<* _ x≢x) = contradiction x≡x x≢x

<-asym : Asymmetric _<_
<-asym (*<* x≤y x≢y) (*<* y≤x _) = x≢y $ ≤-antisym x≤y y≤x

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans {x} {y} {z} x≤y (*<* y≤z y≢z) with x ≟ y
... | yes refl = *<* y≤z y≢z
... | no  x≢y  = *<* (≤-trans x≤y y≤z) λ { refl →
  contradiction (≤-antisym x≤y y≤z) x≢y }

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans {x} {y} {z} (*<* x≤y x≢y) y≤z with y ≟ z
... | yes refl = *<* x≤y x≢y
... | no  y≢z  = ≤-<-trans x≤y (*<* y≤z y≢z)

<-trans : Transitive _<_
<-trans x<y = ≤-<-trans (<⇒≤ x<y)

infix 4 _<?_

postulate
  _<?_ : Decidable _<_

-- <-cmp : Trichotomous _≡_ _<_
-- <-cmp p q with ℤ.<-cmp (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p)
-- ... | tri< < ≢ ≯ = tri< (*<* <)        (≢ ∘ ≡⇒≃) (≯ ∘ drop-*<*)
-- ... | tri≈ ≮ ≡ ≯ = tri≈ (≮ ∘ drop-*<*) (≃⇒≡ ≡)   (≯ ∘ drop-*<*)
-- ... | tri> ≮ ≢ > = tri> (≮ ∘ drop-*<*) (≢ ∘ ≡⇒≃) (*<* >)

-- <-irrelevant : Irrelevant _<_
-- <-irrelevant (*<* p<q₁) (*<* p<q₂) = cong *<* (ℤ.<-irrelevant p<q₁ p<q₂)

-- <-respʳ-≡ : _<_ Respectsʳ _≡_
-- <-respʳ-≡ = subst (_ <_)

-- <-respˡ-≡ : _<_ Respectsˡ _≡_
-- <-respˡ-≡ = subst (_< _)

-- <-resp-≡ : _<_ Respects₂ _≡_
-- <-resp-≡ = <-respʳ-≡ , <-respˡ-≡

-- ------------------------------------------------------------------------
-- -- Structures

-- <-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
-- <-isStrictPartialOrder = record
--   { isEquivalence = isEquivalence
--   ; irrefl        = <-irrefl
--   ; trans         = <-trans
--   ; <-resp-≈      = <-resp-≡
--   }

-- <-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
-- <-isStrictTotalOrder = record
--   { isEquivalence = isEquivalence
--   ; trans         = <-trans
--   ; compare       = <-cmp
--   }

-- ------------------------------------------------------------------------
-- -- Bundles

-- <-strictPartialOrder : StrictPartialOrder 0ℓ 0ℓ 0ℓ
-- <-strictPartialOrder = record
--   { isStrictPartialOrder = <-isStrictPartialOrder
--   }

-- <-strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
-- <-strictTotalOrder = record
--   { isStrictTotalOrder = <-isStrictTotalOrder
--   }
