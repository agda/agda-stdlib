------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership of vectors based on propositional equality,
-- along with some additional definitions.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Membership.Propositional {a} {A : Set a} where

open import Data.Vec using (Vec)
open import Data.Vec.Any using (Any)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Types

infix 4 _∈_ _∉_

_∈_ : A → ∀ {n} → Vec A n → Set _
x ∈ xs = Any (x ≡_) xs

_∉_ : A → ∀ {n} → Vec A n → Set _
x ∉ xs = ¬ x ∈ xs
