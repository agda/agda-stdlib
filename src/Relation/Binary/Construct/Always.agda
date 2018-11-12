------------------------------------------------------------------------
-- The Agda standard library
--
-- The universal binary relation
------------------------------------------------------------------------

module Relation.Binary.Construct.Always where

open import Relation.Binary
open import Relation.Binary.Construct.Constant using (Const)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift)

------------------------------------------------------------------------
-- Definition

Always : ∀ {a ℓ} {A : Set a} → Rel A ℓ
Always = Const (Lift _ ⊤)

------------------------------------------------------------------------
-- Properties

module _ {a} (A : Set a) ℓ where

  refl : Reflexive {ℓ = ℓ} {A} Always
  refl = lift tt

  sym : Symmetric {ℓ = ℓ} {A} Always
  sym _ = lift tt

  trans : Transitive {ℓ = ℓ} {A} Always
  trans _ _ = lift tt

  isEquivalence : IsEquivalence {ℓ = ℓ} {A} Always
  isEquivalence = record {}

  setoid : Setoid a ℓ
  setoid = record
    { isEquivalence = isEquivalence
    }

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.17

Always-setoid = setoid
{-# WARNING_ON_USAGE Always-setoid
"Warning: Always-setoid was deprecated in v0.14.
Please use setoid instead."
#-}
