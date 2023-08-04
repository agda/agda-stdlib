------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on floats
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Float.Properties where

open import Data.Bool.Base as Bool using (Bool)
open import Data.Float.Base
import Data.Maybe.Base as M
import Data.Maybe.Properties as Mₚ
import Data.Nat.Properties as Nₚ
import Data.Word.Base as Word
import Data.Word.Properties as Wₚ
open import Function.Base using (_∘_)
open import Relation.Nullary.Decidable as RN using (map′)
open import Relation.Binary
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.Float.Properties
  renaming (primFloatToWord64Injective to toWord-injective)
  public

------------------------------------------------------------------------
-- Properties of _≈_

≈⇒≡ : _≈_ ⇒ _≡_
≈⇒≡ eq = toWord-injective _ _ (Mₚ.map-injective Wₚ.≈⇒≡ eq)

≈-reflexive : _≡_ ⇒ _≈_
≈-reflexive eq = cong (M.map Word.toℕ ∘ toWord) eq

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
_≈?_ = On.decidable (M.map Word.toℕ ∘ toWord) _≡_ (Mₚ.≡-dec Nₚ._≟_)

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
