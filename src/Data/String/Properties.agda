------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on strings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String.Properties where

open import Data.Bool.Base
open import Data.String.Base

import Data.Char.Properties as Charₚ
import Data.List.Properties as Listₚ

open import Function
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′; ⌊_⌋)
open import Relation.Binary
  using (Decidable; Setoid; DecSetoid; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality.Core
import Data.List.Relation.Binary.Lex.Strict as StrictLex
import Relation.Binary.Construct.On as On
import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.String.Properties public
  renaming ( primStringToListInjective to toList-injective)

------------------------------------------------------------------------
-- Equality

infix 4 _≟_
_≟_ : Decidable {A = String} _≡_
x ≟ y = map′ (toList-injective x y) (cong toList)
      $ Listₚ.≡-dec Charₚ._≟_ (toList x) (toList y)

≡-setoid : Setoid _ _
≡-setoid = PropEq.setoid String

≡-decSetoid : DecSetoid _ _
≡-decSetoid = PropEq.decSetoid _≟_

------------------------------------------------------------------------
-- Lexicographic ordering on strings.

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder =
  On.strictTotalOrder
    (StrictLex.<-strictTotalOrder Charₚ.<-strictTotalOrder)
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

strictTotalOrder = <-strictTotalOrder
{-# WARNING_ON_USAGE strictTotalOrder
"Warning: strictTotalOrder was deprecated in v1.1.
Please use <-strictTotalOrder instead."
#-}
