------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of refinement types
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Refinement.Properties where

open import Data.Refinement.Base
open import Level using (Level; _⊔_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
import Relation.Nullary.Decidable.Core as Dec

private
  variable
    a p : Level
    A : Set a
    P : A → Set p
    v w : [ x ∈ A ∣ P x ]


------------------------------------------------------------------------
-- Basic properties

value-injective : value v ≡ value w → v ≡ w
value-injective refl = refl

module _ (_≈?_ : DecidableEquality A) where

  infix 4 _≡?_
  _≡?_ : DecidableEquality [ x ∈ A ∣ P x ]
  v ≡? w = Dec.map′ value-injective (cong value) (value v ≈? value w)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.4

infix 4 _≟_
_≟_ = _≡?_
{-# WARNING_ON_USAGE _≟_
"Warning: _≟_ was deprecated in v2.4.
Please use _≡?_ instead."
#-}
