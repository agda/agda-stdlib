------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on strings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String.Properties where

open import Data.Bool.Base using (Bool)
import Data.Char.Properties as Charₚ
import Data.List.Properties as Listₚ
import Data.List.Relation.Binary.Pointwise as Pointwise
import Data.List.Relation.Binary.Lex.Strict as StrictLex
open import Data.String.Base
open import Function
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′; ⌊_⌋)
open import Relation.Binary
  using ( _⇒_; Reflexive; Symmetric; Transitive; Substitutive
        ; Decidable; IsPartialEquivalence; IsEquivalence; IsDecEquivalence
        ; PartialSetoid; Setoid; DecSetoid; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality.Core
import Relation.Binary.Construct.On as On
import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.String.Properties public
  renaming ( primStringToListInjective to toList-injective)

------------------------------------------------------------------------
-- Properties of _≈_

≈⇒≡ : _≈_ ⇒ _≡_
≈⇒≡ = toList-injective _ _
    ∘ Pointwise.Pointwise-≡⇒≡
    ∘ Pointwise.map Charₚ.≈⇒≡

≈-reflexive : _≡_ ⇒ _≈_
≈-reflexive = Pointwise.map Charₚ.≈-reflexive
            ∘ Pointwise.≡⇒Pointwise-≡
            ∘ cong toList

≈-refl : Reflexive _≈_
≈-refl {x} = ≈-reflexive {x} {x} refl

≈-sym : Symmetric _≈_
≈-sym = Pointwise.symmetric (λ {i j} → Charₚ.≈-sym {i} {j})

≈-trans : Transitive _≈_
≈-trans = Pointwise.transitive (λ {i j k} → Charₚ.≈-trans {i} {j} {k})

≈-subst : ∀ {ℓ} → Substitutive _≈_ ℓ
≈-subst P x≈y p = subst P (≈⇒≡ x≈y) p

infix 4 _≈?_
_≈?_ : Decidable _≈_
x ≈? y = Pointwise.decidable Charₚ._≈?_ (toList x) (toList y)

≈-isPartialEquivalence : IsPartialEquivalence _≈_
≈-isPartialEquivalence = record
  { sym   = λ {i j} → ≈-sym {i} {j}
  ; trans = λ {i j k} → ≈-trans {i} {j} {k}
  }

≈-partialSetoid : PartialSetoid _ _
≈-partialSetoid = record
  { isPartialEquivalence = ≈-isPartialEquivalence
  }

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence = record
  { isPartialEquivalence = ≈-isPartialEquivalence
  ; refl  = λ {i} → ≈-refl {i}
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

-----------------------------------------------------------------------
-- Properties of _≡_

infix 4 _≟_

_≟_ : Decidable _≡_
x ≟ y = map′ ≈⇒≡ ≈-reflexive $ x ≈? y

≡-setoid : Setoid _ _
≡-setoid = PropEq.setoid String

≡-decSetoid : DecSetoid _ _
≡-decSetoid = PropEq.decSetoid _≟_

------------------------------------------------------------------------
-- Properties of _<_

infix 4 _<?_
_<?_ : Decidable _<_
x <? y = StrictLex.<-decidable Charₚ._≈?_ Charₚ._<?_ (toList x) (toList y)

<-strictTotalOrder-≈ : StrictTotalOrder _ _ _
<-strictTotalOrder-≈ =
  On.strictTotalOrder
    (StrictLex.<-strictTotalOrder Charₚ.<-strictTotalOrder-≈)
    toList

------------------------------------------------------------------------
-- Alternative Boolean equality test.
--
-- Why is the definition _==_ = primStringEquality not used? One
-- reason is that the present definition can sometimes improve type
-- inference, at least with the version of Agda that is current at the
-- time of writing: see unit-test below.

infix 4 _==_
_==_ : String → String → Bool
s₁ == s₂ = ⌊ s₁ ≟ s₂ ⌋

private

  -- The following unit test does not type-check (at the time of
  -- writing) if _==_ is replaced by primStringEquality.

  data P : (String → Bool) → Set where
    p : (c : String) → P (_==_ c)

  unit-test : P (_==_ "")
  unit-test = p _

-- Version 1.1

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
