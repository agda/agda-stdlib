------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}
{-# OPTIONS -WnoUserWarning #-}

module Data.Char.Properties where

open import Data.Bool.Base using (Bool)
open import Data.Char.Base
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_,_)

open import Function.Base
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (map′; isYes)
open import Relation.Binary
import Relation.Binary.Construct.On as On
import Relation.Binary.Construct.Subst.Equality as Subst
import Relation.Binary.Construct.Closure.Reflexive as Refl
import Relation.Binary.Construct.Closure.Reflexive.Properties as Reflₚ
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; cong; sym; trans; subst)

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
_≟_ : Decidable {A = Char} _≡_
x ≟ y = map′ ≈⇒≡ ≈-reflexive (toℕ x ℕₚ.≟ toℕ y)

setoid : Setoid _ _
setoid = PropEq.setoid Char

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_

isDecEquivalence : IsDecEquivalence _≡_
isDecEquivalence = PropEq.isDecEquivalence _≟_

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
_<?_ = On.decidable toℕ ℕ._<_ ℕₚ._<?_

<-cmp : Trichotomous _≡_ _<_
<-cmp c d with ℕₚ.<-cmp (toℕ c) (toℕ d)
... | tri< lt ¬eq ¬gt = tri< lt (≉⇒≢ ¬eq) ¬gt
... | tri≈ ¬lt eq ¬gt = tri≈ ¬lt (≈⇒≡ eq) ¬gt
... | tri> ¬lt ¬eq gt = tri> ¬lt (≉⇒≢ ¬eq) gt

<-irrefl : Irreflexive _≡_ _<_
<-irrefl = ℕₚ.<-irrefl ∘′ cong toℕ

<-trans : Transitive _<_
<-trans {c} {d} {e} = On.transitive toℕ ℕ._<_ ℕₚ.<-trans {c} {d} {e}

<-asym : Asymmetric _<_
<-asym {c} {d} = On.asymmetric toℕ ℕ._<_ ℕₚ.<-asym {c} {d}

<-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
<-isStrictPartialOrder = record
  { isEquivalence = PropEq.isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = λ {a} {b} {c} → <-trans {a} {b} {c}
  ; <-resp-≈      = (λ {c} → PropEq.subst (c <_))
                  , (λ {c} → PropEq.subst (_< c))
  }

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = PropEq.isEquivalence
  ; trans         = λ {a} {b} {c} → <-trans {a} {b} {c}
  ; compare       = <-cmp
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
_≤?_ = Reflₚ.decidable <-cmp

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive = Refl.reflexive

≤-trans : Transitive _≤_
≤-trans = Reflₚ.trans (λ {a} {b} {c} → <-trans {a} {b} {c})

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym = Reflₚ.antisym _≡_ refl ℕₚ.<-asym

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = PropEq.isEquivalence
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

-- Version 1.1

toNat-injective = toℕ-injective
{-# WARNING_ON_USAGE toℕ-injective
"Warning: toNat-injective was deprecated in v1.1.
Please use toℕ-injective instead."
#-}

strictTotalOrder = On.strictTotalOrder ℕₚ.<-strictTotalOrder toℕ
{-# WARNING_ON_USAGE strictTotalOrder
"Warning: strictTotalOrder was deprecated in v1.1.
Please use <-strictTotalOrder-≈ instead."
#-}

-- Version 1.5

infix 4 _≈?_
_≈?_ : Decidable _≈_
x ≈? y = toℕ x ℕₚ.≟ toℕ y
{-# WARNING_ON_USAGE _≈?_
"Warning: _≈?_ was deprecated in v1.5.
Please use _≟_ instead."
#-}

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

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence = record
  { refl  = λ {i} → refl
  ; sym   = λ {i j} → ≈-sym {i} {j}
  ; trans = λ {i j k} → ≈-trans {i} {j} {k}
  }
{-# WARNING_ON_USAGE ≈-isEquivalence
"Warning: ≈-isEquivalence was deprecated in v1.5.
Please use Propositional Equality's isEquivalence instead."
#-}

≈-setoid : Setoid _ _
≈-setoid = record
  { isEquivalence = ≈-isEquivalence
  }
{-# WARNING_ON_USAGE ≈-setoid
"Warning: ≈-setoid was deprecated in v1.5.
Please use Propositional Equality's setoid instead."
#-}

≈-isDecEquivalence : IsDecEquivalence _≈_
≈-isDecEquivalence = record
  { isEquivalence = ≈-isEquivalence
  ; _≟_           = _≈?_
  }
{-# WARNING_ON_USAGE ≈-isDecEquivalence
"Warning: ≈-isDecEquivalence was deprecated in v1.5.
Please use Propositional Equality's isDecEquivalence instead."
#-}

≈-decSetoid : DecSetoid _ _
≈-decSetoid = record
  { isDecEquivalence = ≈-isDecEquivalence
  }
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
<-isStrictPartialOrder-≈ = On.isStrictPartialOrder toℕ ℕₚ.<-isStrictPartialOrder
{-# WARNING_ON_USAGE <-isStrictPartialOrder-≈
"Warning: <-isStrictPartialOrder-≈ was deprecated in v1.5.
Please use <-isStrictPartialOrder instead."
#-}

<-isStrictTotalOrder-≈ : IsStrictTotalOrder _≈_ _<_
<-isStrictTotalOrder-≈ = On.isStrictTotalOrder toℕ ℕₚ.<-isStrictTotalOrder
{-# WARNING_ON_USAGE <-isStrictTotalOrder-≈
"Warning: <-isStrictTotalOrder-≈ was deprecated in v1.5.
Please use <-isStrictTotalOrder instead."
#-}

<-strictPartialOrder-≈ : StrictPartialOrder _ _ _
<-strictPartialOrder-≈ = On.strictPartialOrder ℕₚ.<-strictPartialOrder toℕ
{-# WARNING_ON_USAGE <-strictPartialOrder-≈
"Warning: <-strictPartialOrder-≈ was deprecated in v1.5.
Please use <-strictPartialOrder instead."
#-}

<-strictTotalOrder-≈ : StrictTotalOrder _ _ _
<-strictTotalOrder-≈ = On.strictTotalOrder ℕₚ.<-strictTotalOrder toℕ
{-# WARNING_ON_USAGE <-strictTotalOrder-≈
"Warning: <-strictTotalOrder-≈ was deprecated in v1.5.
Please use <-strictTotalOrder instead."
#-}
