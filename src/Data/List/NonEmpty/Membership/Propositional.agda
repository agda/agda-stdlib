------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional membership over non-empty lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.NonEmpty.Membership.Propositional {a} {A : Set a} where

open import Relation.Binary.PropositionalEquality using (setoid; refl)
open import Data.List.NonEmpty
open import Level
open import Relation.Unary using (Pred)

import Data.List.NonEmpty.Membership.Setoid as SetoidMembership

private
  variable
    p : Level
    P : Pred A p
    xs : List⁺ A

------------------------------------------------------------------------
-- Re-export contents of setoid membership

open SetoidMembership (setoid A) public
