------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties of Real numbers
------------------------------------------------------------------------


{-# OPTIONS --without-K #-}

module Data.PostulatedReal.Properties.Core where

open import Algebra.Bundles
open import Function.Base using (_$_)
open import Data.PostulatedReal.Base
open import Data.Product using (_,_)
open import Data.Sum.Base
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Algebra.Definitions {A = ℝ} _≡_
open import Algebra.Structures  {A = ℝ} _≡_

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

<-cmp : Trichotomous _≡_ _<_
<-cmp x y with x ≟ y
... | yes x≡y = tri≈ (λ x<y → contradiction x≡y $ <⇒≢ x<y) x≡y
                     λ y<x → contradiction x≡y $ ≢-sym $ <⇒≢ y<x
... | no  x≢y with ≤-total x y
... | inj₁ x≤y = tri< (*<* x≤y x≢y) x≢y λ { (*<* y≤x _) →
  contradiction (≤-antisym x≤y y≤x) x≢y }
... | inj₂ x≥y = tri> (λ { (*<* x≤y _) → contradiction
  (≤-antisym x≤y x≥y) x≢y }) x≢y (*<* x≥y $ ≢-sym x≢y)

<-respʳ-≡ : _<_ Respectsʳ _≡_
<-respʳ-≡ = subst (_ <_)

<-respˡ-≡ : _<_ Respectsˡ _≡_
<-respˡ-≡ = subst (_< _)

<-resp-≡ : _<_ Respects₂ _≡_
<-resp-≡ = <-respʳ-≡ , <-respˡ-≡

------------------------------------------------------------------------
-- Structures

<-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = <-resp-≡
  }

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

------------------------------------------------------------------------
-- Bundles

<-strictPartialOrder : StrictPartialOrder 0ℓ 0ℓ 0ℓ
<-strictPartialOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  }

<-strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
<-strictTotalOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder
  }

------------------------------------------------------------------------
-- A specialised module for reasoning about the _≤_ and _<_ relations
------------------------------------------------------------------------

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    (resp₂ _<_)
    <⇒≤
    <-≤-trans
    ≤-<-trans
    public
    hiding (step-≈; step-≈˘)

------------------------------------------------------------------------
-- Properties of _+_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Raw bundles

+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  }

+-rawMonoid : RawMonoid 0ℓ 0ℓ
+-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  ; ε   = 0ℝ
  }

+-0-rawGroup : RawGroup 0ℓ 0ℓ
+-0-rawGroup = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  ; ε   = 0ℝ
  ; _⁻¹ = -_
  }

+-*-rawNearSemiring : RawNearSemiring 0ℓ 0ℓ
+-*-rawNearSemiring = record
  { _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0#  = 0ℝ
  }

+-*-rawSemiring : RawSemiring 0ℓ 0ℓ
+-*-rawSemiring = record
  { _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0#  = 0ℝ
  ; 1#  = 1ℝ
  }

+-*-rawRing : RawRing 0ℓ 0ℓ
+-*-rawRing = record
  { _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_  = -_
  ; 0#  = 0ℝ
  ; 1#  = 1ℝ
  }

------------------------------------------------------------------------
-- Algebraic properties

postulate
  +-assoc     : Associative _+_
  +-comm      : Commutative _+_
  +-identityˡ : LeftIdentity 0ℝ _+_
  +-inverseʳ  : RightInverse 0ℝ -_ _+_

+-identityʳ : RightIdentity 0ℝ _+_
+-identityʳ x rewrite +-comm x 0ℝ = +-identityˡ x

+-identity : Identity 0ℝ _+_
+-identity = +-identityˡ , +-identityʳ

+-inverseˡ : LeftInverse 0ℝ -_ _+_
+-inverseˡ x rewrite +-comm (- x) x = +-inverseʳ x

+-inverse : Inverse 0ℝ -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

-‿cong : Congruent₁ (-_)
-‿cong = cong (-_)

------------------------------------------------------------------------
-- Structures

+-isMagma : IsMagma _+_
+-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        =  cong₂ _+_
  }

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = +-assoc
  }

+-0-isMonoid : IsMonoid _+_ 0ℝ
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identityˡ , +-identityʳ
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ 0ℝ
+-0-isCommutativeMonoid = record
  { isMonoid = +-0-isMonoid
  ; comm   = +-comm
  }

+-0-isGroup : IsGroup _+_ 0ℝ (-_)
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse  = +-inverseˡ , +-inverseʳ
  ; ⁻¹-cong  = -‿cong
  }

+-0-isAbelianGroup : IsAbelianGroup _+_ 0ℝ (-_)
+-0-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm    = +-comm
  }

------------------------------------------------------------------------
-- Packages

+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

+-0-group : Group 0ℓ 0ℓ
+-0-group = record
  { isGroup = +-0-isGroup
  }

+-0-abelianGroup : AbelianGroup 0ℓ 0ℓ
+-0-abelianGroup = record
  { isAbelianGroup = +-0-isAbelianGroup
  }

------------------------------------------------------------------------
-- Properties of _+_ and _≤_

postulate
  +-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_

+-monoˡ-≤ : ∀ z → (_+ z) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ z x≤y = +-mono-≤ x≤y (≤-refl {z})

+-monoʳ-≤ : ∀ z → (_+_ z) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ z x≤y = +-mono-≤ (≤-refl {z}) x≤y

------------------------------------------------------------------------
-- Properties of _+_ and _<_

-- +-mono-<-≤ : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
-- +-mono-<-≤ {x} {y} {z} {w} (*<* x≤y x≢y) z≤w with z ≟ w
-- ... | yes z≡w = *<* (+-mono-≤ x≤y z≤w) $ λ x+z≡y+w → {! x+z≢y+w ?  !}
-- ... | yes z≢w = *<* (+-mono-≤ x≤y z≤w) $ {!   !}

-- +-mono-≤-< : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
-- +-mono-≤-< {x} {y} {z} {w} x≤y z<w rewrite +-comm x z | +-comm y w =
--   +-mono-<-≤ z<w x≤y

-- +-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
-- +-mono-< {x} {y} {z} {w} x<y z<w = <-trans (+-mono-<-≤ x<y (≤-refl {z}))
--   (+-mono-≤-< (≤-refl {y}) z<w)

-- +-monoˡ-< : ∀ z → (_+ z) Preserves _<_ ⟶ _<_
-- +-monoˡ-< z x<y = +-mono-<-≤ x<y (≤-refl {z})

-- +-monoʳ-< : ∀ z → (_+_ z) Preserves _<_ ⟶ _<_
-- +-monoʳ-< z x<y = +-mono-≤-< (≤-refl {z}) x<y





-- TODO (waiting Ring for -‿injective)
------------------------------------------------------------------------
-- Properties of -_ and _≤_/_<_

-- neg-antimono-< : -_ Preserves _<_ ⟶ _>_
-- neg-antimono-< {x} {y} (*<* x≤y x≢y) with ≤-total (- x) (- y)
-- ... | inj₁ -x≤-y = {!   !}
-- ... | inj₂ -x≥-y = *<* -x≥-y $ λ -y≡-x → x≢y $ sym $ -‿injective -y≡-x

-- neg-antimono-≤ : -_ Preserves _≤_ ⟶ _≥_
