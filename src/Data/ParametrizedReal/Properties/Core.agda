------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties of Real numbers
------------------------------------------------------------------------


{-# OPTIONS --without-K --safe #-}

open import Data.ParametrizedReal.Interface

module Data.ParametrizedReal.Properties.Core (RealInterface : Reals) where

open import Algebra.Bundles
import Algebra.Properties.Ring
open import Function.Base using (_$_; _∘_)
open import Data.ParametrizedReal.Base RealInterface
open import Data.Product using (_,_)
open import Data.Sum.Base
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open RealsOps (Reals.ops RealInterface) hiding (_+_; -_; _*_; 1/_) public

open import Algebra.Definitions {A = ℝ} _≡_
open import Algebra.Structures  {A = ℝ} _≡_

private
  variable
    x y z w : ℝ

------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

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
... | *<* x≤0 _ = nonPositive x≤0

nonNeg∧nonZero⇒pos : ∀ x → ⦃ NonNegative x ⦄ → ⦃ NonZero x ⦄ → Positive x
nonNeg∧nonZero⇒pos x ⦃ p ⦄ ⦃ q ⦄
  with NonNegative.nonNegative p | NonZero.nonZero q
... | 0≤x | x≢0 = positive $ *<* 0≤x (≢-sym x≢0)

nonPos∧nonZero⇒neg : ∀ x → ⦃ NonPositive x ⦄ → ⦃ NonZero x ⦄ → Negative x
nonPos∧nonZero⇒neg x ⦃ p ⦄ ⦃ q ⦄
  with NonPositive.nonPositive p | NonZero.nonZero q
... | x≤0 | x≢0 = negative $ *<* x≤0 x≢0

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

infix 4 _≤?_
_≤?_ : Decidable _≤_
x ≤? y with ≤-total x y
... | inj₁ x≤y = yes x≤y
... | inj₂ x≥y with x ≟ y
... | yes refl = yes ≤-refl
... | no  x≢y  = no λ x≤y → contradiction (≤-antisym x≤y x≥y) x≢y

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
_<?_ : Decidable _<_
x <? y with x ≟ y
... | yes x≡y = no λ { (*<* _ x≢y) → contradiction x≡y x≢y }
... | no  x≢y with x ≤? y
... | yes x≤y = yes $ *<* x≤y x≢y
... | no  x≰y = no λ { (*<* x≤y _) → x≰y x≤y }

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

+-identityʳ : RightIdentity 0ℝ _+_
+-identityʳ x rewrite +-comm x 0ℝ = +-identityˡ x

+-identity : Identity 0ℝ _+_
+-identity = +-identityˡ , +-identityʳ

+-inverseʳ : RightInverse 0ℝ -_ _+_
+-inverseʳ x rewrite +-comm x (- x) = +-inverseˡ x

+-inverse : Inverse 0ℝ -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

-‿cong : Congruent₁ (-_)
-‿cong = cong (-_)

-x≡0⇒x≡0 : - x ≡ 0ℝ → x ≡ 0ℝ
-x≡0⇒x≡0 {x} -x≡0 = begin
  x       ≡˘⟨ +-identityʳ x ⟩
  x + 0ℝ  ≡˘⟨ cong (x +_) -x≡0 ⟩
  x + - x ≡⟨ +-inverseʳ x ⟩
  0ℝ      ∎
  where open ≡-Reasoning

x≡0⇒-x≡0 : x ≡ 0ℝ → - x ≡ 0ℝ
x≡0⇒-x≡0 {x} x≡0 = begin
  - x      ≡˘⟨ +-identityʳ (- x) ⟩
  - x + 0ℝ ≡˘⟨ cong (- x +_) x≡0 ⟩
  - x + x  ≡⟨ +-inverseˡ x ⟩
  0ℝ       ∎
  where open ≡-Reasoning

-x≢0 : x ≢ 0ℝ → - x ≢ 0ℝ
-x≢0 p = p ∘ -x≡0⇒x≡0

instance
  -x-nonZero : .⦃ _ : NonZero x ⦄ → NonZero (- x)
  -x-nonZero {x} = ≢-nonZero $ -x≢0 (≢-nonZero⁻¹ x)

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

x+x≡0⇒x≡0 : x + x ≡ 0ℝ → x ≡ 0ℝ
x+x≡0⇒x≡0 {x} x+x≡0 with x ≟ 0ℝ
... | yes x≡0 = x≡0
... | no  x≢0 with x ≤? 0ℝ
... | yes x≤0 = let
  x<0 = *<* x≤0 x≢0
  x+x<0+0 = +-mono-< x<0 x<0
  x+x≢0 = λ x+x≡0 → <⇒≢ x+x<0+0 $ trans x+x≡0 (sym $ +-identityˡ 0ℝ)
  in contradiction x+x≡0 x+x≢0
... | no  x≰0 = let
  x>0 = ≰⇒> x≰0
  x+x>0+0 = +-mono-< x>0 x>0
  x+x≢0 = λ x+x≡0 → <⇒≢ x+x>0+0 $ sym $ trans x+x≡0 (sym $ +-identityˡ 0ℝ)
  in contradiction x+x≡0 x+x≢0

-x≡x⇒x≡0 : - x ≡ x → x ≡ 0ℝ
-x≡x⇒x≡0 {x} -x≡x = x+x≡0⇒x≡0 $ begin
  x + x ≡˘⟨ cong (x +_) -x≡x ⟩
  x - x ≡⟨ +-inverseʳ x ⟩
  0ℝ    ∎
  where open ≡-Reasoning

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

*-identityʳ : RightIdentity 1ℝ _*_
*-identityʳ x rewrite *-comm x 1ℝ = *-identityˡ x

*-identity : Identity 1ℝ _*_
*-identity = *-identityˡ , *-identityʳ

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ x y z rewrite *-comm (y + z) x | *-comm y x | *-comm z x =
      *-distribˡ-+ x y z

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-assoc-middle : ∀ x y z w → ((x * y) * (z * w)) ≡ (x * (y * z)) * w
*-assoc-middle x y z w = begin
  (x * y) * (z * w) ≡˘⟨ *-assoc (x * y) z w ⟩
  ((x * y) * z) * w ≡⟨ cong (_* w) (*-assoc x y z) ⟩
  (x * (y * z)) * w ∎
  where open ≡-Reasoning

*-comm-middle : ∀ x y z w → (x * y) * (z * w) ≡ (x * z) * (y * w)
*-comm-middle x y z w = begin
  (x * y) * (z * w) ≡⟨ *-assoc-middle x y z w ⟩
  (x * (y * z)) * w ≡⟨ cong (λ y → (x * y) * w) (*-comm y z) ⟩
  (x * (z * y)) * w ≡˘⟨ *-assoc-middle x z y w ⟩
  (x * z) * (y * w) ∎
  where open ≡-Reasoning

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

*-inverseʳ : ∀ x .⦃ _ : NonZero x ⦄ → x * (1/ x) ≡ 1ℝ
*-inverseʳ x = trans (*-comm x (1/ x)) (*-inverseˡ x)

*-cancelˡ : ∀ x .⦃ _ : NonZero x ⦄ {y z} → x * y ≡ x * z → y ≡ z
*-cancelˡ x {y} {z} xy≡xz = begin
              y  ≡⟨ helper y ⟩
  1/ x * (x * y) ≡⟨ cong (1/ x *_) xy≡xz ⟩
  1/ x * (x * z) ≡˘⟨ helper z ⟩
              z  ∎
  where
  open ≡-Reasoning
  helper : ∀ y → y ≡ 1/ x * (x * y)
  helper y = sym $ begin
    1/ x * (x * y) ≡˘⟨ *-assoc (1/ x) x y ⟩
    (1/ x * x) * y ≡⟨ (cong (_* y) $ *-inverseˡ x) ⟩
    1ℝ * y         ≡⟨ *-identityˡ y ⟩
    y              ∎

*-cancelʳ : ∀ x .⦃ _ : NonZero x ⦄ {y z} → y * x ≡ z * x → y ≡ z
*-cancelʳ x {y} {z} yx≡zx rewrite *-comm x y | *-comm z x =
  *-cancelˡ x $ trans (*-comm x y) yx≡zx

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

-1² : -1ℝ * -1ℝ ≡ 1ℝ
-1² rewrite sym $ -‿distribʳ-* -1ℝ 1ℝ | *-identityʳ -1ℝ = -‿involutive 1ℝ

*-cancel-neg : (x y : ℝ) → - x * - y ≡ x * y
*-cancel-neg x y rewrite sym (*-neg-identityˡ x) | sym (*-neg-identityˡ y)
  | *-comm-middle -1ℝ x -1ℝ y | -1² = *-identityˡ (x * y)

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

neg-cancel-≤ : ∀ {x y} → - x ≤ - y → y ≤ x
neg-cancel-≤ {x} {y} -x≤-y = begin
  y     ≡˘⟨ -‿involutive y ⟩
  - - y ≤⟨ neg-antimono-≤ -x≤-y ⟩
  - - x ≡⟨ -‿involutive x ⟩
  x     ∎
  where
  open ≤-Reasoning

-x≥0⇒x≤0 : - x ≥ 0ℝ → x ≤ 0ℝ
-x≥0⇒x≤0 {x} -x≥0 = neg-cancel-≤ $ ≤-trans (≤-reflexive $ -0#≈0#) -x≥0

-x≤0⇒x≥0 : - x ≤ 0ℝ → x ≥ 0ℝ
-x≤0⇒x≥0 {x} -x≤0 = neg-cancel-≤ $ ≤-trans -x≤0 (≤-reflexive $ sym -0#≈0#)

x≥0⇒-x≤0 : x ≥ 0ℝ → - x ≤ 0ℝ
x≥0⇒-x≤0 {x} x≥0 = ≤-trans (neg-antimono-≤ x≥0) (≤-reflexive -0#≈0#)

x≤0⇒-x≥0 : x ≤ 0ℝ → - x ≥ 0ℝ
x≤0⇒-x≥0 {x} x≤0 = ≤-trans (≤-reflexive $ sym -0#≈0#) (neg-antimono-≤ x≤0)

x≥0∧-x≥0⇒x≡0 : x ≥ 0ℝ → - x ≥ 0ℝ → x ≡ 0ℝ
x≥0∧-x≥0⇒x≡0 {x} x≥0 -x≥0 = ≤-antisym (-x≥0⇒x≤0 -x≥0) x≥0

x≤0∧-x≤0⇒x≡0 : x ≤ 0ℝ → - x ≤ 0ℝ → x ≡ 0ℝ
x≤0∧-x≤0⇒x≡0 {x} x≤0 -x≤0 = ≤-antisym x≤0 (-x≤0⇒x≥0 -x≤0)

x≥0⇒-x≤x : x ≥ 0ℝ → - x ≤ x
x≥0⇒-x≤x x≥0 = ≤-trans (x≥0⇒-x≤0 x≥0) x≥0

x≤0⇒-x≥x : x ≤ 0ℝ → - x ≥ x
x≤0⇒-x≥x x≤0 = ≤-trans x≤0 (x≤0⇒-x≥0 x≤0)

------------------------------------------------------------------------
-- Properties of _*_ and _≤_

*-monoˡ-≤-nonNeg : ∀ z .⦃ _ : NonNegative z ⦄ → (z *_) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-nonNeg z {x} {y} rewrite *-comm z x | *-comm z y =
  *-monoʳ-≤-nonNeg z

*-monoʳ-≤-nonPos : ∀ z .⦃ _ : NonPositive z ⦄ → (_* z) Preserves _≤_ ⟶ _≥_
*-monoʳ-≤-nonPos z ⦃ p ⦄ {x} {y} x≤y = neg-cancel-≤ $ begin
  - (x * z) ≡⟨ -‿distribʳ-* x z ⟩
  x * - z   ≤⟨ *-monoʳ-≤-nonNeg (- z) ⦃ q p ⦄ x≤y ⟩
  y * - z   ≡˘⟨ -‿distribʳ-* y z ⟩
  - (y * z) ∎
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

*-cancelʳ-≤-pos : ∀ z .⦃ _ : Positive z ⦄ → x * z ≤ y * z → x ≤ y
*-cancelʳ-≤-pos {x} {y} z xz≤yz with ≤-total x y
... | inj₁ x≤y = x≤y
... | inj₂ x≥y with ≤-antisym xz≤yz $ *-monoʳ-≤-nonNeg z
  ⦃ pos⇒nonNeg z ⦄ x≥y
... | xz≡yz = ≤-reflexive $ *-cancelʳ z ⦃ pos⇒nonZero z ⦄ xz≡yz

*-cancelˡ-≤-pos : ∀ z .⦃ _ : Positive z ⦄ → z * x ≤ z * y → x ≤ y
*-cancelˡ-≤-pos {x} {y} z rewrite *-comm z x | *-comm z y = *-cancelʳ-≤-pos z

*-cancelʳ-≤-neg : ∀ z .⦃ _ : Negative z ⦄ → x * z ≤ y * z → x ≥ y
*-cancelʳ-≤-neg {x} {y} z ⦃ p ⦄ xz≤yz = neg-cancel-≤ $
  *-cancelʳ-≤-pos (- z) ⦃ q p ⦄ $ begin
  - x * - z    ≡˘⟨ -‿distribˡ-* x (- z) ⟩
  - (x * - z)  ≡˘⟨ -‿cong (-‿distribʳ-* x z) ⟩
  - - (x * z)  ≡⟨ -‿involutive (x * z) ⟩
  x * z        ≤⟨ xz≤yz ⟩
  y * z        ≡˘⟨ -‿involutive (y * z) ⟩
  - - (y * z)  ≡⟨ -‿cong (-‿distribʳ-* y z) ⟩
  - (y * - z)  ≡⟨ -‿distribˡ-* y (- z) ⟩
  - y * - z    ∎
  where
  open ≤-Reasoning
  q : Negative z → Positive (- z)
  q p with Negative.negative p
  ... | *<* z≤0 z≢0 = positive $ *<* (begin
    0ℝ   ≡⟨ trans (sym $ *-zeroˡ (- 1ℝ)) (*-neg-identityʳ 0ℝ) ⟩
    - 0ℝ ≤⟨ neg-antimono-≤ z≤0 ⟩
    - z  ∎) (≢-sym $ -x≢0 $ z≢0)

*-cancelˡ-≤-neg : ∀ z .⦃ _ : Negative z ⦄ → z * x ≤ z * y → x ≥ y
*-cancelˡ-≤-neg {x} {y} z rewrite *-comm z x | *-comm z y =
  *-cancelʳ-≤-neg z

*-mono-≥0 : x ≥ 0ℝ → y ≥ 0ℝ → x * y ≥ 0ℝ
*-mono-≥0 {x} {y} x≥0 y≥0 = begin
  0ℝ     ≡˘⟨ *-zeroʳ x ⟩
  x * 0ℝ ≤⟨ *-monoˡ-≤-nonNeg x ⦃ nonNegative x≥0 ⦄ y≥0 ⟩
  x * y  ∎
  where open ≤-Reasoning

*-mono-≤0 : x ≤ 0ℝ → y ≤ 0ℝ → x * y ≥ 0ℝ
*-mono-≤0 {x} {y} x≤0 y≤0 = begin
  0ℝ     ≡˘⟨ *-zeroʳ x ⟩
  x * 0ℝ ≤⟨ *-monoˡ-≤-nonPos x ⦃ nonPositive x≤0 ⦄ y≤0 ⟩
  x * y  ∎
  where open ≤-Reasoning

*-mono-≥0-≤0 : x ≥ 0ℝ → y ≤ 0ℝ → x * y ≤ 0ℝ
*-mono-≥0-≤0 {x} {y} x≥0 y≤0 = begin
  x * y  ≤⟨ *-monoˡ-≤-nonNeg x ⦃ nonNegative x≥0 ⦄ y≤0 ⟩
  x * 0ℝ ≡⟨ *-zeroʳ x ⟩
  0ℝ     ∎
  where open ≤-Reasoning

*-mono-≤0-≥0 : x ≤ 0ℝ → y ≥ 0ℝ → x * y ≤ 0ℝ
*-mono-≤0-≥0 {x} {y} x≤0 y≥0 rewrite *-comm x y = *-mono-≥0-≤0 y≥0 x≤0

------------------------------------------------------------------------
-- Properties of _*_ and _<_

*-monoˡ-<-pos : ∀ z .⦃ _ : Positive z ⦄ → (z *_) Preserves _<_ ⟶ _<_
*-monoˡ-<-pos z (*<* x≤y x≢y) = *<*
  (*-monoˡ-≤-nonNeg z ⦃ pos⇒nonNeg z ⦄ x≤y)
  λ zx≡zy → contradiction (*-cancelˡ z ⦃ pos⇒nonZero z ⦄ zx≡zy) x≢y

*-monoʳ-<-pos : ∀ z .⦃ _ : Positive z ⦄ → (_* z) Preserves _<_ ⟶ _<_
*-monoʳ-<-pos z {x} {y} rewrite *-comm x z | *-comm y z = *-monoˡ-<-pos z

*-cancelˡ-<-nonNeg : ∀ z .⦃ _ : NonNegative z ⦄ → ∀ {x y} → z * x < z * y → x < y
*-cancelˡ-<-nonNeg z ⦃ p ⦄ {x} {y} (*<* zx≤zy zx≢zy) with z ≟ 0ℝ
... | yes refl = contradiction (trans (*-zeroˡ x) (sym $ *-zeroˡ y)) zx≢zy
... | no  z≢0  = *<*
  (*-cancelˡ-≤-pos z ⦃ nonNeg∧nonZero⇒pos _ ⦃ p ⦄ ⦃ ≢-nonZero z≢0 ⦄ ⦄ zx≤zy)
  λ x≡y → contradiction (cong (z *_) x≡y) zx≢zy

*-cancelʳ-<-nonNeg : ∀ z .⦃ _ : NonNegative z ⦄ → ∀ {x y} → x * z < y * z → x < y
*-cancelʳ-<-nonNeg z {x} {y} rewrite *-comm x z | *-comm y z = *-cancelˡ-<-nonNeg z

*-monoˡ-<-neg : ∀ z .⦃ _ : Negative z ⦄ → (z *_) Preserves _<_ ⟶ _>_
*-monoˡ-<-neg z (*<* x≤y x≢y) = *<*
  (*-monoˡ-≤-nonPos z ⦃ neg⇒nonPos z ⦄ x≤y)
  λ zy≡zx → contradiction (*-cancelˡ z ⦃ neg⇒nonZero z ⦄ $ sym zy≡zx) x≢y

*-monoʳ-<-neg : ∀ z .⦃ _ : Negative z ⦄ → (_* z) Preserves _<_ ⟶ _>_
*-monoʳ-<-neg z {x} {y} rewrite *-comm x z | *-comm y z = *-monoˡ-<-neg z

*-cancelˡ-<-nonPos : ∀ z .⦃ _ : NonPositive z ⦄ → z * x < z * y → x > y
*-cancelˡ-<-nonPos {x} {y} z ⦃ p ⦄ (*<* zx≤zy zx≢zy) with z ≟ 0ℝ
... | yes refl = contradiction (trans (*-zeroˡ x) (sym $ *-zeroˡ y)) zx≢zy
... | no  z≢0  = *<*
  (*-cancelˡ-≤-neg z ⦃ nonPos∧nonZero⇒neg _ ⦃ p ⦄ ⦃ ≢-nonZero z≢0 ⦄ ⦄ zx≤zy)
  λ y≡x → contradiction (cong (z *_) $ sym y≡x) zx≢zy

*-cancelʳ-<-nonPos : ∀ z .⦃ _ : NonPositive z ⦄ → x * z < y * z → x > y
*-cancelʳ-<-nonPos {x} {y} z rewrite *-comm x z | *-comm y z =
  *-cancelˡ-<-nonPos z

------------------------------------------------------------------------
-- Properties of 1/_
------------------------------------------------------------------------

1/1 : 1/ 1ℝ ≡ 1ℝ
1/1 rewrite sym $ *-identityˡ (1/ 1ℝ) = *-inverseʳ 1ℝ

1/x≢0 : {x : ℝ} → (p : x ≢ 0ℝ) → (1/ x) ⦃ ≢-nonZero p ⦄ ≢ 0ℝ
1/x≢0 {x} p 1/x≡0 = p $ begin
  x            ≡˘⟨ *-identityʳ x ⟩
  x * 1ℝ       ≡˘⟨ cong (_*_ x) (*-inverseʳ x) ⟩
  x * (x / x)  ≡⟨ cong (λ y → x * (x * y)) 1/x≡0 ⟩
  x * (x * 0ℝ) ≡⟨ cong (_*_ x) (*-zeroʳ x) ⟩
  x * 0ℝ       ≡⟨ *-zeroʳ x ⟩
  0ℝ ∎
  where
  open ≡-Reasoning
  instance _ = ≢-nonZero p

nonZero⇒1/nonZero : ∀ x .⦃ _ : NonZero x ⦄ → NonZero (1/ x)
nonZero⇒1/nonZero x = ≢-nonZero $ 1/x≢0 (≢-nonZero⁻¹ x)

1/-involutive : ∀ x .⦃ _ : NonZero x ⦄ → (1/(1/ x)) ⦃ nonZero⇒1/nonZero x ⦄ ≡ x
1/-involutive x = begin
  1/(1/ x)
    ≡˘⟨ *-identityˡ (1/(1/ x)) ⟩
  1ℝ * 1/(1/ x)
    ≡˘⟨ (cong (_* 1/(1/ x)) $ *-inverseʳ (1/ x)) ⟩
  1/ x * 1/(1/ x) * 1/(1/ x)
    ≡˘⟨ *-identityˡ (1/ x * 1/(1/ x) * 1/(1/ x)) ⟩
  1ℝ * (1/ x * 1/(1/ x) * 1/(1/ x))
    ≡˘⟨ ((cong (_* (1/ x * 1/(1/ x) * 1/(1/ x))) $ *-inverseʳ x )) ⟩
  (x * 1/ x) * (1/ x * 1/(1/ x) * 1/(1/ x))
    ≡⟨ *-assoc x (1/ x) (1/ x * 1/(1/ x) * 1/(1/ x)) ⟩
  x * (1/ x * (1/ x * 1/(1/ x) * 1/(1/ x)))
    ≡⟨ (cong (λ y → x * (1/ x * y)) $ *-assoc (1/ x) (1/(1/ x)) (1/(1/ x))) ⟩
  x * (1/ x * (1/ x * (1/(1/ x) * 1/(1/ x))))
    ≡˘⟨ (cong (_*_ x) $ *-assoc (1/ x) (1/ x) (1/(1/ x) * 1/(1/ x))) ⟩
  x * ((1/ x * 1/ x) * (1/(1/ x) * 1/(1/ x)))
    ≡⟨ (cong (_*_ x) $ *-comm-middle (1/ x) (1/ x) (1/(1/ x)) (1/(1/ x))) ⟩
  x * ((1/ x * 1/(1/ x)) * (1/ x * 1/(1/ x)))
    ≡⟨ ((cong (_*_ x) $ cong₂ _*_ (*-inverseʳ (1/ x)) (*-inverseʳ (1/ x)))) ⟩
  x * (1ℝ * 1ℝ)
    ≡⟨ trans (cong (_*_ x) $ *-identityʳ 1ℝ) (*-identityʳ x) ⟩
  x ∎
  where
  open ≡-Reasoning
  instance _ = nonZero⇒1/nonZero x

x*y≡0 : ∀ x y → x * y ≡ 0ℝ → x ≡ 0ℝ ⊎ y ≡ 0ℝ
x*y≡0 x y xy≡0 with x ≟ 0ℝ
... | yes x≡0 = inj₁ x≡0
... | no  x≢0   with y ≟ 0ℝ
... | yes y≡0 = inj₂ y≡0
... | no  y≢0   = contradiction (begin
    y                ≡˘⟨ *-identityˡ y ⟩
    1ℝ * y           ≡˘⟨ cong (_* y) (*-inverseʳ x) ⟩
    (x / x) * y     ≡⟨ *-assoc x (1/ x) y ⟩
    x * (1/ x * y)  ≡⟨ cong (_*_ x) (*-comm (1/ x) y) ⟩
    x * (y * 1/ x)  ≡˘⟨ *-assoc x y (1/ x) ⟩
    x * y * 1/ x    ≡⟨ cong (_* 1/ x) xy≡0 ⟩
    0ℝ * 1/ x       ≡⟨ *-zeroˡ (1/ x) ⟩
    0ℝ ∎) y≢0
  where
  open ≡-Reasoning
  instance _ = ≢-nonZero x≢0

x*y≢0 : x ≢ 0ℝ → y ≢ 0ℝ → x * y ≢ 0ℝ
x*y≢0 {x} {y} p q xy≡0 with x*y≡0 x y xy≡0
... | inj₁ x≡0 = p x≡0
... | inj₂ y≡0 = q y≡0

x*y-nonZero : ∀ x y .⦃ _ : NonZero x ⦄ .⦃ _ : NonZero y ⦄ → NonZero (x * y)
x*y-nonZero x y = ≢-nonZero $
  x*y≢0 (≢-nonZero⁻¹ x) (≢-nonZero⁻¹ y)

1/-distrib-* : ∀ x y .⦃ _ : NonZero x ⦄ .⦃ _ : NonZero y ⦄ →
  (1/(x * y)) ⦃ x*y-nonZero x y ⦄ ≡ 1/ x * 1/ y
1/-distrib-* x y = sym $ begin
    1/ x * 1/ y
      ≡˘⟨ *-identityʳ (1/ x * 1/ y) ⟩
    1/ x * 1/ y * 1ℝ
      ≡˘⟨ cong (_*_ (1/ x * 1/ y)) (*-inverseʳ (x * y) ⦃ _ ⦄) ⟩
    1/ x * 1/ y * ((x * y) * 1/ (x * y))
      ≡˘⟨ *-assoc (1/ x * 1/ y) (x * y) (1/ (x * y)) ⟩
    (1/ x * 1/ y * (x * y)) * (1/ (x * y))
      ≡⟨ cong (_* (1/ (x * y))) (*-comm-middle (1/ x) (1/ y) x y) ⟩
    (1/ x * x) * (1/ y * y) * 1/ (x * y)
      ≡⟨ cong₂ (λ a b → a * b * 1/ (x * y)) (*-inverseˡ x) (*-inverseˡ y) ⟩
    1ℝ * 1ℝ * 1/ (x * y)
      ≡⟨ cong (_* 1/ (x * y) ) (*-identityˡ 1ℝ) ⟩
    1ℝ * 1/ (x * y)
      ≡⟨ *-identityˡ (1/ (x * y)) ⟩
    1/ (x * y) ∎
    where
    open ≡-Reasoning
    instance _ = x*y-nonZero x y

private
  1/pos-neg-helper : .⦃ _ : NonZero x ⦄ → x * 0ℝ ≤ x * 1/ x
  1/pos-neg-helper {x} = begin
    x * 0ℝ   ≡⟨ *-zeroʳ x ⟩
    0ℝ       ≤⟨ 0≤1 ⟩
    1ℝ       ≡˘⟨ *-inverseʳ x ⟩
    x * 1/ x ∎
    where open ≤-Reasoning

1/pos⇒pos : ∀ x ⦃ _ : Positive x ⦄ → Positive ((1/ x) ⦃ pos⇒nonZero x ⦄)
1/pos⇒pos x ⦃ p ⦄ with Positive.positive p
... | *<* 0≤x 0≢x = positive $ *<* help (≢-sym $ 1/x≢0 $ ≢-sym 0≢x)
  where
  instance _ = pos⇒nonZero x
  help : 0ℝ ≤ (1/ x)
  help = *-cancelˡ-≤-pos x 1/pos-neg-helper

1/neg⇒neg : ∀ x ⦃ _ : Negative x ⦄ → Negative ((1/ x) ⦃ neg⇒nonZero x ⦄)
1/neg⇒neg x ⦃ p ⦄ with Negative.negative p
... | *<* x≤0 x≢0 = negative $ *<* help (1/x≢0 x≢0)
  where
  instance _ = neg⇒nonZero x
  help : (1/ x) ≤ 0ℝ
  help = *-cancelˡ-≤-neg x 1/pos-neg-helper

pos⇒1/pos : ∀ x .⦃ _ : NonZero x ⦄ ⦃ _ : Positive (1/ x) ⦄ → Positive x
pos⇒1/pos x = subst Positive (1/-involutive x) (1/pos⇒pos (1/ x))

neg⇒1/neg : ∀ x .⦃ _ : NonZero x ⦄ ⦃ _ : Negative (1/ x) ⦄ → Negative x
neg⇒1/neg x = subst Negative (1/-involutive x) (1/neg⇒neg (1/ x))

------------------------------------------------------------------------
-- Properties of _/_
------------------------------------------------------------------------

/-mul : (x y z w : ℝ) .⦃ _ : NonZero y ⦄ .⦃ _ : NonZero w ⦄ →
  (x / y) * (z / w) ≡ ((x * z) / (y * w)) ⦃ x*y-nonZero y w ⦄
/-mul x y z w = begin
  (x / y) * (z / w)         ≡⟨ *-comm-middle x (1/ y) z (1/ w) ⟩
  (x * z) * (1/ y * 1/ w)   ≡˘⟨ cong (_*_ (x * z))  (1/-distrib-* y w) ⟩
  ((x * z) / (y * w)) ⦃ x*y-nonZero y w ⦄ ∎
  where open ≡-Reasoning

x/1 : ∀ x → x / 1ℝ ≡ x
x/1 x rewrite 1/1 = *-identityʳ x

/-simplˡ : ∀ x y z .⦃ _ : NonZero x ⦄ .⦃ _ : NonZero z ⦄ →
  ((x * y) / (x * z))  ⦃ x*y-nonZero x z ⦄ ≡ y / z
/-simplˡ x y z ⦃ p ⦄ rewrite sym (/-mul x x y z) | *-inverseʳ x ⦃ p ⦄ =
  *-identityˡ (y / z)

/-simplʳ : ∀ x y z .⦃ _ : NonZero x ⦄ .⦃ q : NonZero z ⦄ →
  ((y * x) / (z * x))  ⦃ x*y-nonZero z x ⦄ ≡ y / z
/-simplʳ x y z ⦃ p ⦄ rewrite sym (/-mul y z x x) | *-inverseʳ x ⦃ p ⦄ =
  *-identityʳ (y / z)

/-coef : ∀ x y z .⦃ _ : NonZero z ⦄ → x * y / z ≡ (x * y) / z
/-coef x y z ⦃ p ⦄ rewrite sym (x/1 x) | /-mul x 1ℝ y z ⦃ 1-nonZero ⦄ ⦃ p ⦄
  | x/1 x | 1/-distrib-* 1ℝ z ⦃ 1-nonZero ⦄ ⦃ p ⦄ | 1/1
  | *-identityˡ (1/ z) = refl

