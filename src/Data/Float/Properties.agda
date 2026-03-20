------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on floats
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Float.Properties where

open import Data.Bool.Base as Bool using (Bool)
open import Data.Float.Base using (Float; _≈_; toWord64)
import Data.Maybe.Base as Maybe using (Maybe; just; nothing; map)
import Data.Maybe.Properties as Maybe using (map-injective; ≡-dec)
import Data.Nat.Properties as ℕ using (_≟_)
import Data.Word64.Base as Word64 using (Word64; toℕ)
import Data.Word64.Properties as Word64 using (≈⇒≡)
open import Function.Base using (_∘_)
open import Relation.Nullary.Decidable as RN using (map′)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Bundles using (Setoid; DecSetoid)
open import Relation.Binary.Structures
  using (IsEquivalence; IsDecEquivalence)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; Substitutive; Decidable; DecidableEquality)
import Relation.Binary.Construct.On as On using (decidable)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (setoid; decSetoid)

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.Float.Properties
  renaming (primFloatToWord64Injective to toWord64-injective)
  public

------------------------------------------------------------------------
-- Properties of _≈_

≈⇒≡ : _≈_ ⇒ _≡_
≈⇒≡ eq = toWord64-injective _ _ (Maybe.map-injective Word64.≈⇒≡ eq)

≈-reflexive : _≡_ ⇒ _≈_
≈-reflexive eq = cong (Maybe.map Word64.toℕ ∘ toWord64) eq

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
_≈?_ = On.decidable (Maybe.map Word64.toℕ ∘ toWord64) _≡_ (Maybe.≡-dec ℕ._≟_)

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
_≟_ : DecidableEquality Float
x ≟ y = map′ ≈⇒≡ ≈-reflexive (x ≈? y)

≡-setoid : Setoid _ _
≡-setoid = setoid Float

≡-decSetoid : DecSetoid _ _
≡-decSetoid = decSetoid _≟_


------------------------------------------------------------------------
-- DEPRECATIONS

toWord-injective = toWord64-injective
{-# WARNING_ON_USAGE toWord-injective
"Warning: toWord-injective was deprecated in v2.1.
Please use toWord64-injective instead."
#-}
