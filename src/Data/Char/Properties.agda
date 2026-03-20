------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char.Properties where

open import Data.Bool.Base using (Bool)
open import Data.Char.Base using (Char; _≈_; _≉_; _<_; _≤_; toℕ)
import Data.Nat.Base as ℕ using (ℕ; _<_; _≤_)
import Data.Nat.Properties as ℕ
  using (_<?_; <-cmp; <-isStrictPartialOrder; <-isStrictTotalOrder
        ; <-strictPartialOrder; <-strictTotalOrder; <-irrefl; <-trans; <-asym
        ; _≟_)
open import Data.Product.Base using (_,_)
open import Function.Base using (const; _∘′_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (map′; isYes)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Bundles
  using (Setoid; DecSetoid; StrictPartialOrder; StrictTotalOrder; Preorder
        ; Poset; DecPoset)
open import Relation.Binary.Structures
  using (IsDecEquivalence; IsStrictPartialOrder; IsStrictTotalOrder
        ; IsPreorder; IsPartialOrder; IsDecPartialOrder; IsEquivalence)
open import Relation.Binary.Definitions
  using (Decidable; DecidableEquality; Trichotomous; Irreflexive
        ; Transitive; Asymmetric; Antisymmetric; Symmetric; Substitutive
        ; Reflexive; tri<; tri≈; tri>)
import Relation.Binary.Construct.On as On
  using (decidable; transitive; asymmetric; isStrictPartialOrder
        ; isStrictTotalOrder; strictPartialOrder; strictTotalOrder)
import Relation.Binary.Construct.Closure.Reflexive as Refl
  using (Refl; reflexive)
import Relation.Binary.Construct.Closure.Reflexive.Properties as Refl
  using (trans; antisym; decidable)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≢_; refl; cong; sym; trans; subst)
import Relation.Binary.PropositionalEquality.Properties as ≡ using
  (isDecEquivalence; setoid; decSetoid; isEquivalence)

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.Char.Properties
  renaming ( primCharToNatInjective to toℕ-injective)
  public

------------------------------------------------------------------------
-- Properties of _≈_

≈⇒≡ : _≈_ ⇒ _≡_
≈⇒≡ = toℕ-injective _ _

≉⇒≢ : _≉_ ⇒ _≢_
≉⇒≢ p refl = p refl

≈-reflexive : _≡_ ⇒ _≈_
≈-reflexive = cong toℕ

------------------------------------------------------------------------
-- Properties of _≡_

infix 4 _≟_
_≟_ : DecidableEquality Char
x ≟ y = map′ ≈⇒≡ ≈-reflexive (toℕ x ℕ.≟ toℕ y)

setoid : Setoid _ _
setoid = ≡.setoid Char

decSetoid : DecSetoid _ _
decSetoid = ≡.decSetoid _≟_

isDecEquivalence : IsDecEquivalence _≡_
isDecEquivalence = ≡.isDecEquivalence _≟_

------------------------------------------------------------------------
-- Boolean equality test.
--
-- Why is the definition _==_ = primCharEquality not used? One reason
-- is that the present definition can sometimes improve type
-- inference, at least with the version of Agda that is current at the
-- time of writing: see unit-test below.

infix 4 _==_
_==_ : Char → Char → Bool
c₁ == c₂ = isYes (c₁ ≟ c₂)

private

  -- The following unit test does not type-check (at the time of
  -- writing) if _==_ is replaced by primCharEquality.

  data P : (Char → Bool) → Set where
    MkP : (c : Char) → P (c ==_)

  unit-test : P ('x' ==_)
  unit-test = MkP _

------------------------------------------------------------------------
-- Properties of _<_

infix 4 _<?_
_<?_ : Decidable _<_
_<?_ = On.decidable toℕ ℕ._<_ ℕ._<?_

<-cmp : Trichotomous _≡_ _<_
<-cmp c d with ℕ.<-cmp (toℕ c) (toℕ d)
... | tri< lt ¬eq ¬gt = tri< lt (≉⇒≢ ¬eq) ¬gt
... | tri≈ ¬lt eq ¬gt = tri≈ ¬lt (≈⇒≡ eq) ¬gt
... | tri> ¬lt ¬eq gt = tri> ¬lt (≉⇒≢ ¬eq) gt

<-irrefl : Irreflexive _≡_ _<_
<-irrefl = ℕ.<-irrefl ∘′ cong toℕ

<-trans : Transitive _<_
<-trans {c} {d} {e} = On.transitive toℕ ℕ._<_ ℕ.<-trans {c} {d} {e}

<-asym : Asymmetric _<_
<-asym {c} {d} = On.asymmetric toℕ ℕ._<_ ℕ.<-asym {c} {d}

<-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
<-isStrictPartialOrder = record
  { isEquivalence = ≡.isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = λ {a} {b} {c} → <-trans {a} {b} {c}
  ; <-resp-≈      = (λ {c} → ≡.subst (c <_))
                  , (λ {c} → ≡.subst (_< c))
  }

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  ; compare              = <-cmp
  }

<-strictPartialOrder : StrictPartialOrder _ _ _
<-strictPartialOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  }

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder
  }

------------------------------------------------------------------------
-- Properties of _≤_

infix 4 _≤?_
_≤?_ : Decidable _≤_
_≤?_ = Refl.decidable <-cmp

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive = Refl.reflexive

≤-trans : Transitive _≤_
≤-trans = Refl.trans (λ {a} {b} {c} → <-trans {a} {b} {c})

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym = Refl.antisym _≡_ refl ℕ.<-asym

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = ≡.isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isDecPartialOrder : IsDecPartialOrder _≡_ _≤_
≤-isDecPartialOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; _≟_            = _≟_
  ; _≤?_           = _≤?_
  }

≤-preorder : Preorder _ _ _
≤-preorder = record { isPreorder = ≤-isPreorder }

≤-poset : Poset _ _ _
≤-poset = record { isPartialOrder = ≤-isPartialOrder }

≤-decPoset : DecPoset _ _ _
≤-decPoset = record { isDecPartialOrder = ≤-isDecPartialOrder }

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.5

≈-refl : Reflexive _≈_
≈-refl = refl
{-# WARNING_ON_USAGE ≈-refl
"Warning: ≈-refl was deprecated in v1.5.
Please use Propositional Equality's refl instead."
#-}

≈-sym : Symmetric _≈_
≈-sym = sym
{-# WARNING_ON_USAGE ≈-sym
"Warning: ≈-sym was deprecated in v1.5.
Please use Propositional Equality's sym instead."
#-}

≈-trans : Transitive _≈_
≈-trans = trans
{-# WARNING_ON_USAGE ≈-trans
"Warning: ≈-trans was deprecated in v1.5.
Please use Propositional Equality's trans instead."
#-}

≈-subst : ∀ {ℓ} → Substitutive _≈_ ℓ
≈-subst P x≈y p = subst P (≈⇒≡ x≈y) p
{-# WARNING_ON_USAGE ≈-subst
"Warning: ≈-subst was deprecated in v1.5.
Please use Propositional Equality's subst instead."
#-}

infix 4 _≈?_
_≈?_ : Decidable _≈_
x ≈? y = toℕ x ℕ.≟ toℕ y

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }
≈-setoid : Setoid _ _
≈-setoid = record
  { isEquivalence = ≈-isEquivalence
  }
≈-isDecEquivalence : IsDecEquivalence _≈_
≈-isDecEquivalence = record
  { isEquivalence = ≈-isEquivalence
  ; _≟_           = _≈?_
  }
≈-decSetoid : DecSetoid _ _
≈-decSetoid = record
  { isDecEquivalence = ≈-isDecEquivalence
  }
{-# WARNING_ON_USAGE _≈?_
"Warning: _≈?_ was deprecated in v1.5.
Please use _≟_ instead."
#-}
{-# WARNING_ON_USAGE ≈-isEquivalence
"Warning: ≈-isEquivalence was deprecated in v1.5.
Please use Propositional Equality's isEquivalence instead."
#-}
{-# WARNING_ON_USAGE ≈-setoid
"Warning: ≈-setoid was deprecated in v1.5.
Please use Propositional Equality's setoid instead."
#-}
{-# WARNING_ON_USAGE ≈-isDecEquivalence
"Warning: ≈-isDecEquivalence was deprecated in v1.5.
Please use Propositional Equality's isDecEquivalence instead."
#-}
{-# WARNING_ON_USAGE ≈-decSetoid
"Warning: ≈-decSetoid was deprecated in v1.5.
Please use Propositional Equality's decSetoid instead."
#-}

≡-setoid : Setoid _ _
≡-setoid = setoid
{-# WARNING_ON_USAGE ≡-setoid
"Warning: ≡-setoid was deprecated in v1.5.
Please use setoid instead."
#-}

≡-decSetoid : DecSetoid _ _
≡-decSetoid = decSetoid
{-# WARNING_ON_USAGE ≡-decSetoid
"Warning: ≡-decSetoid was deprecated in v1.5.
Please use decSetoid instead."
#-}

<-isStrictPartialOrder-≈ : IsStrictPartialOrder _≈_ _<_
<-isStrictPartialOrder-≈ = On.isStrictPartialOrder toℕ ℕ.<-isStrictPartialOrder
{-# WARNING_ON_USAGE <-isStrictPartialOrder-≈
"Warning: <-isStrictPartialOrder-≈ was deprecated in v1.5.
Please use <-isStrictPartialOrder instead."
#-}

<-isStrictTotalOrder-≈ : IsStrictTotalOrder _≈_ _<_
<-isStrictTotalOrder-≈ = On.isStrictTotalOrder toℕ ℕ.<-isStrictTotalOrder
{-# WARNING_ON_USAGE <-isStrictTotalOrder-≈
"Warning: <-isStrictTotalOrder-≈ was deprecated in v1.5.
Please use <-isStrictTotalOrder instead."
#-}

<-strictPartialOrder-≈ : StrictPartialOrder _ _ _
<-strictPartialOrder-≈ = On.strictPartialOrder ℕ.<-strictPartialOrder toℕ
{-# WARNING_ON_USAGE <-strictPartialOrder-≈
"Warning: <-strictPartialOrder-≈ was deprecated in v1.5.
Please use <-strictPartialOrder instead."
#-}

<-strictTotalOrder-≈ : StrictTotalOrder _ _ _
<-strictTotalOrder-≈ = On.strictTotalOrder ℕ.<-strictTotalOrder toℕ
{-# WARNING_ON_USAGE <-strictTotalOrder-≈
"Warning: <-strictTotalOrder-≈ was deprecated in v1.5.
Please use <-strictTotalOrder instead."
#-}

