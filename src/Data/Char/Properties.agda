------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char.Properties where

open import Data.Bool.Base using (Bool)
open import Data.Char.Base

import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕₚ

open import Function
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (map′; isYes)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core
import Relation.Binary.Construct.On as On
import Relation.Binary.Construct.Closure.Reflexive as Refl
import Relation.Binary.Construct.Closure.Reflexive.Properties as Reflₚ
import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.Char.Properties
  renaming ( primCharToNatInjective to toℕ-injective)
  public

------------------------------------------------------------------------
-- Properties of _≈_

≈⇒≡ : _≈_ ⇒ _≡_
≈⇒≡ = toℕ-injective _ _

≉⇒≢ : ∀ {x y} → ¬ (x ≈ y) → x ≢ y
≉⇒≢ p refl = p refl

≈-reflexive : _≡_ ⇒ _≈_
≈-reflexive = cong toℕ

≈-refl : Reflexive _≈_
≈-refl = refl

≈-sym : Symmetric _≈_
≈-sym = sym

≈-trans : Transitive _≈_
≈-trans = trans

≈-subst : ∀ {ℓ} → Substitutive _≈_ ℓ
≈-subst P x≈y p = subst P (≈⇒≡ x≈y) p

infix 4 _≈?_
_≈?_ : Decidable _≈_
x ≈? y = toℕ x ℕₚ.≟ toℕ y

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence = record
  { refl  = λ {i} → ≈-refl {i}
  ; sym   = λ {i j} → ≈-sym {i} {j}
  ; trans = λ {i j k} → ≈-trans {i} {j} {k}
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

------------------------------------------------------------------------
-- Properties of _≡_

infix 4 _≟_
_≟_ : Decidable {A = Char} _≡_
x ≟ y = map′ ≈⇒≡ ≈-reflexive (x ≈? y)

≡-setoid : Setoid _ _
≡-setoid = PropEq.setoid Char

≡-decSetoid : DecSetoid _ _
≡-decSetoid = PropEq.decSetoid _≟_

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

<-trans : Transitive _<_
<-trans {c} {d} {e} = On.transitive toℕ ℕ._<_ ℕₚ.<-trans {c} {d} {e}

<-asym : Asymmetric _<_
<-asym {c} {d} = On.asymmetric toℕ ℕ._<_ ℕₚ.<-asym {c} {d}

<-isStrictPartialOrder-≈ : IsStrictPartialOrder _≈_ _<_
<-isStrictPartialOrder-≈ = On.isStrictPartialOrder toℕ ℕₚ.<-isStrictPartialOrder

<-isStrictTotalOrder-≈ : IsStrictTotalOrder _≈_ _<_
<-isStrictTotalOrder-≈ = On.isStrictTotalOrder toℕ ℕₚ.<-isStrictTotalOrder

<-strictPartialOrder-≈ : StrictPartialOrder _ _ _
<-strictPartialOrder-≈ = On.strictPartialOrder ℕₚ.<-strictPartialOrder toℕ

<-strictTotalOrder-≈ : StrictTotalOrder _ _ _
<-strictTotalOrder-≈ = On.strictTotalOrder ℕₚ.<-strictTotalOrder toℕ

<-cmp-≈ : Trichotomous _≈_ _<_
<-cmp-≈ c d = ℕₚ.<-cmp (toℕ c) (toℕ d)

<-cmp : Trichotomous _≡_ _<_
<-cmp c d with ℕₚ.<-cmp (toℕ c) (toℕ d)
... | tri< lt ¬eq ¬gt = tri< lt (≉⇒≢ ¬eq) ¬gt
... | tri≈ ¬lt eq ¬gt = tri≈ ¬lt (≈⇒≡ eq) ¬gt
... | tri> ¬lt ¬eq gt = tri> ¬lt (≉⇒≢ ¬eq) gt

------------------------------------------------------------------------
-- Properties of _≤_

infix 4 _≤?_
_≤?_ : Decidable _≤_
_≤?_ = Reflₚ.decidable <-cmp

≤-reflexive-≈ : _≈_ ⇒ _≤_
≤-reflexive-≈ = Refl.reflexive ∘′ ≈⇒≡

≤-trans : Transitive _≤_
≤-trans = Reflₚ.trans (λ {c} {d} {e} → <-trans {c} {d} {e})

≤-antisym : Antisymmetric _≈_ _≤_
≤-antisym = Reflₚ.antisym _≈_ (λ {c} → ≈-refl {c}) (λ {c} {d} → <-asym {c} {d})

≤-isPreorder-≈ : IsPreorder _≈_ _≤_
≤-isPreorder-≈ = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive     = ≤-reflexive-≈
  ; trans         = ≤-trans
  }

≤-isPartialOrder-≈ : IsPartialOrder _≈_ _≤_
≤-isPartialOrder-≈ = record
  { isPreorder = ≤-isPreorder-≈
  ; antisym    = ≤-antisym
  }

≤-isDecPartialOrder-≈ : IsDecPartialOrder _≈_ _≤_
≤-isDecPartialOrder-≈ = record
  { isPartialOrder = ≤-isPartialOrder-≈
  ; _≟_            = _≈?_
  ; _≤?_           = _≤?_
  }

≤-preorder-≈ : Preorder _ _ _
≤-preorder-≈ = record { isPreorder = ≤-isPreorder-≈ }

≤-poset-≈ : Poset _ _ _
≤-poset-≈ = record { isPartialOrder = ≤-isPartialOrder-≈ }

≤-decPoset-≈ : DecPoset _ _ _
≤-decPoset-≈ = record { isDecPartialOrder = ≤-isDecPartialOrder-≈ }

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

setoid = ≡-setoid
{-# WARNING_ON_USAGE setoid
"Warning: setoid was deprecated in v1.1.
Please use ≡-setoid instead."
#-}

decSetoid = ≡-decSetoid
{-# WARNING_ON_USAGE decSetoid
"Warning: decSetoid was deprecated in v1.1.
Please use ≡-decSetoid instead."
#-}

strictTotalOrder = <-strictTotalOrder-≈
{-# WARNING_ON_USAGE strictTotalOrder
"Warning: strictTotalOrder was deprecated in v1.1.
Please use <-strictTotalOrder-≈ instead."
#-}
