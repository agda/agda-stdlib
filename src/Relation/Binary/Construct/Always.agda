------------------------------------------------------------------------
-- The Agda standard library
--
-- The universal binary relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Always where

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Construct.Constant using (Const)
open import Data.Unit.Polymorphic using (⊤; tt)

------------------------------------------------------------------------
-- Definition

Always : ∀ {a ℓ} {A : Set a} → Rel A ℓ
Always = Const ⊤

------------------------------------------------------------------------
-- Properties

module _ {a} (A : Set a) ℓ where

  refl : Reflexive {A = A} {ℓ = ℓ} Always
  refl = _

  sym : Symmetric {A = A} {ℓ = ℓ} Always
  sym _ = _

  trans : Transitive {A = A} {ℓ = ℓ} Always
  trans _ _ = _

  isEquivalence : IsEquivalence {ℓ = ℓ} {A} Always
  isEquivalence = record {}

  setoid : Setoid a ℓ
  setoid = record
    { isEquivalence = isEquivalence
    }
