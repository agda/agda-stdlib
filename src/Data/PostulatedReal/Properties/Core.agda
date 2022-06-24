------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties of Real numbers
------------------------------------------------------------------------


{-# OPTIONS --without-K #-}

module Data.PostulatedReal.Properties.Core where

open import Algebra.Bundles
import Algebra.Properties.Ring
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
-- Basic properties of sign predicates
------------------------------------------------------------------------

pos⇒nonNeg : ∀ x → ⦃ Positive x ⦄ → NonNegative x
pos⇒nonNeg x ⦃ p ⦄ with Positive.positive p
... | *<* 0≤x _ = nonNegative 0≤x

neg⇒nonPos : ∀ x → ⦃ Negative x ⦄ → NonPositive x
neg⇒nonPos x ⦃ p ⦄ with Negative.negative p
... | *<* x≤0 + = nonPositive x≤0

nonNeg∧nonZero⇒pos : ∀ x → ⦃ NonNegative x ⦄ → ⦃ NonZero x ⦄ → Positive x
nonNeg∧nonZero⇒pos x ⦃ p ⦄ ⦃ q ⦄
  with NonNegative.nonNegative p | NonZero.nonZero q
... | 0≤x | x≢0 = positive $ *<* 0≤x (≢-sym x≢0)

pos⇒nonZero : ∀ x → ⦃ Positive x ⦄ → NonZero x
pos⇒nonZero x ⦃ p ⦄ with Positive.positive p
... | *<* _ 0≢x = ≢-nonZero $ ≢-sym 0≢x

neg⇒nonZero : ∀ x → ⦃ Negative x ⦄ → NonZero x
neg⇒nonZero x ⦃ p ⦄ with Negative.negative p
... | *<* _ x≢0 = ≢-nonZero $ x≢0

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

+-monoˡ-< : ∀ z → (_+ z) Preserves _<_ ⟶ _<_
+-monoˡ-< z {x} {y} x<y = *<* (+-monoˡ-≤ z (<⇒≤ x<y)) λ x+z≡y+z →
  (<⇒≢ x<y) $ begin
  x           ≡˘⟨ +-identityʳ x ⟩
  x + 0ℝ      ≡˘⟨ (cong (x +_) $ +-inverseʳ z) ⟩
  x + (z - z) ≡˘⟨ +-assoc x z (- z) ⟩
  (x + z) - z ≡⟨ (cong (_- z) $ x+z≡y+z) ⟩
  (y + z) - z ≡⟨ +-assoc y z (- z) ⟩
  y + (z - z) ≡⟨ (cong (y +_) $ +-inverseʳ z) ⟩
  y + 0ℝ      ≡⟨ +-identityʳ y ⟩
  y           ∎
  where open ≡-Reasoning

+-monoʳ-< : ∀ z → (z +_) Preserves _<_ ⟶ _<_
+-monoʳ-< z {x} {y} rewrite +-comm z x | +-comm z y = +-monoˡ-< z

+-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< {_} {y} {z} x<y z<w = <-trans (+-monoˡ-< z x<y)
  (+-monoʳ-< y z<w)

+-mono-<-≤ : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {_} {y} {z} x<y z≤w = <-≤-trans (+-monoˡ-< z x<y)
  (+-monoʳ-≤ y z≤w)

+-mono-≤-< : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-mono-≤-< {x} {y} {z} {w} x≤y z<w rewrite +-comm x z | +-comm y w =
  +-mono-<-≤ z<w x≤y

------------------------------------------------------------------------
-- Properties of _*_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Raw bundles

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  }

*-rawMonoid : RawMonoid 0ℓ 0ℓ
*-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  ; ε   = 1ℝ
  }

------------------------------------------------------------------------
-- Algebraic properties

postulate
  *-assoc         : Associative _*_
  *-comm          : Commutative _*_
  *-identityˡ     : LeftIdentity 1ℝ _*_
  *-distribˡ-+    : _*_ DistributesOverˡ _+_
  *-neg-identityˡ : (x : ℝ) → -1ℝ * x ≡ - x

*-identityʳ : RightIdentity 1ℝ _*_
*-identityʳ x rewrite *-comm x 1ℝ = *-identityˡ x

*-identity : Identity 1ℝ _*_
*-identity = *-identityˡ , *-identityʳ

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ x y z rewrite *-comm (y + z) x | *-comm y x | *-comm z x =
      *-distribˡ-+ x y z

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-zeroˡ : LeftZero 0ℝ _*_
*-zeroˡ x = begin
  0ℝ * x               ≡⟨ cong (_* x) (sym (+-inverseʳ 1ℝ)) ⟩
  (1ℝ + -1ℝ) * x       ≡⟨ *-distribʳ-+ x 1ℝ -1ℝ ⟩
  (1ℝ * x) + (-1ℝ * x) ≡⟨ cong₂ _+_ (*-identityˡ x) (*-neg-identityˡ x) ⟩
  x + (- x)            ≡⟨ +-inverseʳ x ⟩
  0ℝ                   ∎
  where open ≡-Reasoning

*-zeroʳ : RightZero 0ℝ _*_
*-zeroʳ x rewrite *-comm x 0ℝ = *-zeroˡ x

*-zero : Zero 0ℝ _*_
*-zero = *-zeroˡ , *-zeroʳ

*-neg-identityʳ : (x : ℝ) → x * -1ℝ ≡ - x
*-neg-identityʳ x = trans (*-comm x -1ℝ) (*-neg-identityˡ x)


postulate
  *-inverseˡ : ∀ x .⦃ _ : NonZero x  ⦄ → (1/ x) * x ≡ 1ℝ

*-inverseʳ : ∀ x .⦃ _ : NonZero x ⦄ → x * (1/ x) ≡ 1ℝ
*-inverseʳ x = trans (*-comm x (1/ x)) (*-inverseˡ x)

------------------------------------------------------------------------
-- Structures

*-isMagma : IsMagma _*_
*-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        =  cong₂ _*_
  }

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = *-assoc
  }

*-1-isMonoid : IsMonoid _*_ 1ℝ
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identityˡ , *-identityʳ
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1ℝ
*-1-isCommutativeMonoid = record
  { isMonoid = *-1-isMonoid
  ; comm     = *-comm
  }

+-*-isRing : IsRing _+_ _*_ -_ 0ℝ 1ℝ
+-*-isRing = record
  { +-isAbelianGroup = +-0-isAbelianGroup
  ; *-cong           = *-1-isMonoid .IsMonoid.∙-cong
  ; *-assoc          = *-1-isMonoid .IsMonoid.assoc
  ; *-identity       = *-1-isMonoid .IsMonoid.identity
  ; distrib          = *-distribˡ-+ , *-distribʳ-+
  ; zero             = *-zeroˡ , *-zeroʳ
  }

+-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0ℝ 1ℝ
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

------------------------------------------------------------------------
-- Packages

*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { isMonoid = *-1-isMonoid
  }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

+-*-ring : Ring 0ℓ 0ℓ
+-*-ring = record
  { isRing = +-*-isRing
  }

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }

open Algebra.Properties.Ring record
  { Carrier = ℝ
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = 0ℝ
  ; 1# = 1ℝ
  ; isRing = +-*-isRing
  } public

------------------------------------------------------------------------
-- Properties of -_ and _≤_/_<_

neg-antimono-≤ : -_ Preserves _≤_ ⟶ _≥_
neg-antimono-≤ {x} {y} x≤y = begin
  - y           ≡˘⟨ +-identityʳ (- y) ⟩
  - y + 0ℝ      ≤⟨ +-monoʳ-≤ (- y) 0≤y-x ⟩
  - y + (y - x) ≡˘⟨ +-assoc (- y) y (- x) ⟩
  (- y + y) - x ≡⟨ (cong (_- x) $ +-inverseˡ y) ⟩
  0ℝ - x        ≡⟨ +-identityˡ (- x) ⟩
  - x           ∎
  where
  open ≤-Reasoning
  0≤y-x = begin
    0ℝ    ≡˘⟨ +-inverseʳ x ⟩
    x - x ≤⟨ +-monoˡ-≤ (- x) x≤y ⟩
    y - x ∎

neg-antimono-< : -_ Preserves _<_ ⟶ _>_
neg-antimono-< {x} {y} (*<* x≤y x≢y) = *<* (neg-antimono-≤ x≤y)
  λ -y≡-x → x≢y $ sym $ -‿injective -y≡-x

------------------------------------------------------------------------
-- Properties of _*_ and _≤_

postulate
  *-monoʳ-≤-nonNeg : ∀ z .⦃ _ : NonNegative z ⦄ → (_* z) Preserves _≤_ ⟶ _≤_

*-monoˡ-≤-nonNeg : ∀ z .⦃ _ : NonNegative z ⦄ → (z *_) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-nonNeg z {x} {y} rewrite *-comm z x | *-comm z y =
  *-monoʳ-≤-nonNeg z

*-monoʳ-≤-nonPos : ∀ z .⦃ _ : NonPositive z ⦄ → (_* z) Preserves _≤_ ⟶ _≥_
*-monoʳ-≤-nonPos z ⦃ p ⦄ {x} {y} x≤y = begin
  y * z       ≡˘⟨ -‿involutive (y * z) ⟩
  - - (y * z) ≡⟨ (cong (-_) $ -‿distribʳ-* y z) ⟩
  - (y * - z) ≤⟨ neg-antimono-≤ (*-monoʳ-≤-nonNeg (- z) ⦃ q p ⦄ x≤y) ⟩
  - (x * - z) ≡˘⟨ (cong (-_) $ -‿distribʳ-* x z) ⟩
  - - (x * z) ≡⟨ -‿involutive (x * z) ⟩
  x * z       ∎
  where
  open ≤-Reasoning
  q : NonPositive z → NonNegative (- z)
  q p = nonNegative $ begin
    0ℝ   ≡⟨ trans (sym $ *-zeroˡ (- 1ℝ)) (*-neg-identityʳ 0ℝ) ⟩
    - 0ℝ ≤⟨ neg-antimono-≤ (NonPositive.nonPositive p) ⟩
    - z  ∎

*-monoˡ-≤-nonPos : ∀ z .⦃ _ : NonPositive z ⦄ → (z *_) Preserves _≤_ ⟶ _≥_
*-monoˡ-≤-nonPos z {x} {y} rewrite *-comm z x | *-comm z y =
  *-monoʳ-≤-nonPos z

*-cancelʳ-≤-neg : ∀ z .⦃ _ : Negative z ⦄ → x * z ≤ y * z → x ≥ y
*-cancelʳ-≤-neg {x} {y} z ⦃ p ⦄ xz≤yz = begin
  y             ≡˘⟨ *-identityʳ y ⟩
  y * 1ℝ        ≡˘⟨ (cong (y *_) $ *-inverseʳ z ⦃ z-nonZero p ⦄) ⟩
  y * (z * 1/z) ≡˘⟨ *-assoc y z 1/z ⟩
  (y * z) * 1/z ≤⟨ *-monoʳ-≤-nonPos 1/z ⦃ {!   !} ⦄ xz≤yz ⟩
  (x * z) * 1/z ≡⟨ *-assoc x z 1/z ⟩
  x * (z * 1/z) ≡⟨ (cong (x *_) $ *-inverseʳ z ⦃ z-nonZero p ⦄) ⟩
  x * 1ℝ        ≡⟨ *-identityʳ x ⟩
  x             ∎
  where
  open ≤-Reasoning
  z-nonZero : Negative z → NonZero z
  z-nonZero p = neg⇒nonZero _ ⦃ p ⦄
  1/z = (1/ z) ⦃ z-nonZero p ⦄

*-cancelˡ-≤-neg : ∀ z .⦃ _ : Negative z ⦄ → z * x ≤ z * y → x ≥ y
*-cancelˡ-≤-neg {x} {y} z rewrite *-comm z x | *-comm z y =
  *-cancelʳ-≤-neg z






