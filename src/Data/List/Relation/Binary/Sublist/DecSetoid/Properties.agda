-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the decidable setoid sublist relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecSetoid)

module Data.List.Relation.Binary.Sublist.DecSetoid.Properties
       {c ℓ} (S : DecSetoid c ℓ)
       where

open import Data.List.Base using (length)
open import Data.List.Relation.Binary.Sublist.DecSetoid S
open import Relation.Binary using (Decidable)

private
  module S = DecSetoid S

------------------------------------------------------------------------
-- Properties common to the setoid version

import Data.List.Relation.Binary.Sublist.Setoid.Properties S.setoid as SubProp
open SubProp
  hiding ( sublist?
         )
  public

------------------------------------------------------------------------
-- Special properties holding for the special DecSetoid case

sublist? : Decidable _⊆_
sublist? = SubProp.sublist? S._≟_
