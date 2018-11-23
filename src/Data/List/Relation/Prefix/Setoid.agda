------------------------------------------------------------------------
-- The Agda standard library
--
-- The prefix relation over setoid equality.
------------------------------------------------------------------------

open import Relation.Binary using (Setoid; IsPreorder; Preorder; IsEquivalence)

module Data.List.Relation.Prefix.Setoid
  {c ℓ} (S : Setoid c ℓ) where

open import Data.List using (List)
open import Data.List.Membership.Setoid S using (_∈_)
open import Data.List.Relation.Prefix.Heterogeneous
open import Data.List.Relation.Prefix.Heterogeneous.Properties
open import Data.List.Relation.Pointwise hiding (isPreorder; preorder)
open import Level using (_⊔_)
open import Relation.Nullary using (¬_)

open Setoid S using () renaming (Carrier to A)
module S = Setoid S

------------------------------------------------------------------------
-- Definitions

isPreorder : IsPreorder {A = List A} (Pointwise S._≈_) (Prefix S._≈_)
isPreorder = record
  { isEquivalence = isEquivalence S.isEquivalence
  ; reflexive     = fromPointwise
  ; trans         = trans S.trans }

preorder : Preorder _ _ _
preorder = record { isPreorder = isPreorder }
