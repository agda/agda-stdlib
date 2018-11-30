------------------------------------------------------------------------
-- The Agda standard library
--
-- Data.Vec.Any.Membership instantiated with propositional equality,
-- along with some additional definitions.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Vec.Membership.Propositional {a} {A : Set a} where

open import Data.Vec using (Vec)
open import Data.Vec.Any using (Any)
open import Relation.Binary.PropositionalEquality using (setoid; subst)

import Data.Vec.Membership.Setoid as SetoidMembership

------------------------------------------------------------------------
-- Re-export contents of setoid membership

open SetoidMembership (setoid A) public hiding (lose)

------------------------------------------------------------------------
-- Other operations

lose : ∀ {p} {P : A → Set p} {x n} {xs : Vec A n} → x ∈ xs → P x → Any P xs
lose = SetoidMembership.lose (setoid A) (subst _)
