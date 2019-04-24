------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char.Properties where

open import Data.Bool using (Bool)
open import Data.Char.Base

import Data.Nat.Properties as ℕₚ

open import Function
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′;  ⌊_⌋)
open import Relation.Binary
  using (Decidable; Setoid; DecSetoid; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality.Core
import Relation.Binary.Construct.On as On
import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.Char.Properties
  renaming ( primCharToNatInjective to toNat-injective)
  public

------------------------------------------------------------------------
-- Decidable equality

infix 4 _≟_
_≟_ : Decidable {A = Char} _≡_
x ≟ y = map′ (toNat-injective x y) (cong toNat)
      $ toNat x ℕₚ.≟ toNat y

------------------------------------------------------------------------
-- Boolean equality test.
--
-- Why is the definition _==_ = primCharEquality not used? One reason
-- is that the present definition can sometimes improve type
-- inference, at least with the version of Agda that is current at the
-- time of writing: see unit-test below.

infix 4 _==_
_==_ : Char → Char → Bool
c₁ == c₂ = ⌊ c₁ ≟ c₂ ⌋

private

  -- The following unit test does not type-check (at the time of
  -- writing) if _==_ is replaced by primCharEquality.

  data P : (Char → Bool) → Set where
    p : (c : Char) → P (c ==_)

  unit-test : P ('x' ==_)
  unit-test = p _

------------------------------------------------------------------------
-- Structures

≡-setoid : Setoid _ _
≡-setoid = PropEq.setoid Char

≡-decSetoid : DecSetoid _ _
≡-decSetoid = PropEq.decSetoid _≟_

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = On.strictTotalOrder ℕₚ.<-strictTotalOrder toNat


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

strictTotalOrder = <-strictTotalOrder
{-# WARNING_ON_USAGE strictTotalOrder
"Warning: strictTotalOrder was deprecated in v1.1.
Please use <-strictTotalOrder instead."
#-}
