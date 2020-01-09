------------------------------------------------------------------------
-- The Agda standard library
--
-- Equality over container extensions parametrised by some setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.Container.Relation.Binary.Equality.Setoid {c e} (S : Setoid c e) where

open import Level using (_⊔_; suc)
open import Relation.Binary

open import Data.Container.Core
open import Data.Container.Relation.Binary.Pointwise
import Data.Container.Relation.Binary.Pointwise.Properties as Pw

private
  module S = Setoid S
open S using (_≈_) renaming (Carrier to X)

------------------------------------------------------------------------
-- Definition of equality

module _ {s p} (C : Container s p) where

  Eq : Rel (⟦ C ⟧ X) (e ⊔ s ⊔ p)
  Eq = Pointwise C _≈_

------------------------------------------------------------------------
-- Relational properties

  refl : Reflexive Eq
  refl = Pw.refl C _ S.refl

  sym : Symmetric Eq
  sym = Pw.sym C _ S.sym

  trans : Transitive Eq
  trans = Pw.trans C _ S.trans

  isEquivalence : IsEquivalence Eq
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  setoid : Setoid (s ⊔ p ⊔ c) (s ⊔ p ⊔ e)
  setoid = record
    { isEquivalence = isEquivalence
    }
