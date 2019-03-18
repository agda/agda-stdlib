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
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality.Core
import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.String.Properties
  renaming ( primStringToListInjective to toList-injective)
  public

------------------------------------------------------------------------
-- Decidable equality

infix 4 _≟_
_≟_ : Decidable {A = String} _≡_
x ≟ y = map′ (toList-injective x y) (cong toList)
      $ Listₚ.≡-dec Charₚ._≟_ (toList x) (toList y)

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_

------------------------------------------------------------------------
-- Boolean equality test.
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
