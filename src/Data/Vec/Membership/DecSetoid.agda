------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable setoid membership over vectors.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecSetoid)

module Data.Vec.Membership.DecSetoid {c ℓ} (DS : DecSetoid c ℓ) where

open import Data.Vec using (Vec)
open import Data.Vec.Relation.Unary.Any using (any)
open import Relation.Nullary using (Dec)
open DecSetoid DS renaming (Carrier to A)

------------------------------------------------------------------------
-- Re-export contents of propositional membership

open import Data.Vec.Membership.Setoid setoid public

------------------------------------------------------------------------
-- Other operations

infix 4 _∈?_

_∈?_ : ∀ x {n} (xs : Vec A n) → Dec (x ∈ xs)
x ∈? xs = any (x ≟_) xs
