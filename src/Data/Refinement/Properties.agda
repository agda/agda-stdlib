------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of refinement types
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Refinement.Properties where

open import Level
open import Data.Refinement.Base
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

module _ (eq? : DecidableEquality A) where

  infix 4 _≟_
  _≟_ : DecidableEquality [ x ∈ A ∣ P x ]
  v ≟ w = Dec.map′ value-injective (cong value) (eq? (value v) (value w))
