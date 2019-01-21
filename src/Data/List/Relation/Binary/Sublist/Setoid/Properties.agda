-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the setoid sublist relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Sublist.Setoid.Properties {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Base using (length)
open import Data.List.Relation.Sublist.Setoid S
import Data.List.Relation.Equality.Setoid S as Pw

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Properties common to the heterogeneous version

import Data.List.Relation.Sublist.Heterogeneous.Properties as SubProp
open SubProp
  hiding (trans)
  public

------------------------------------------------------------------------
-- Special properties holding for the special Setoid case

private
  module S = Setoid S

reflexive : _≡_ ⇒ _⊆_
reflexive P.refl = fromPointwise Pw.≋-refl

refl : Reflexive _⊆_
refl = reflexive P.refl

trans : Transitive _⊆_
trans = SubProp.trans S.trans
