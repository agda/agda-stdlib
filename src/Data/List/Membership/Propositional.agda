------------------------------------------------------------------------
-- The Agda standard library
--
-- Data.List.Any.Membership instantiated with propositional equality,
-- along with some additional definitions.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Membership.Propositional {a} {A : Set a} where

open import Data.List.Relation.Unary.Any using (Any)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; resp)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

import Data.List.Membership.Setoid as SetoidMembership

------------------------------------------------------------------------
-- Re-export contents of setoid membership

open SetoidMembership (setoid A) public hiding (lose)

------------------------------------------------------------------------
-- Different members

infix 4 _≢∈_

_≢∈_ : ∀ {x y : A} {xs} → x ∈ xs → y ∈ xs → Set _
_≢∈_ x∈xs y∈xs = ∀ x≡y → resp (_∈ _) x≡y x∈xs ≢ y∈xs

------------------------------------------------------------------------
-- Other operations

lose : ∀ {p} {P : A → Set p} {x xs} → x ∈ xs → P x → Any P xs
lose = SetoidMembership.lose (setoid A) (resp _)
