------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable setoid membership over fresh lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecSetoid)

module Data.List.Fresh.Membership.DecSetoid {a ℓ} (DS : DecSetoid a ℓ) where

open import Level using (Level)
open import Data.List.Fresh.Relation.Unary.Any using (any?)
import Data.List.Fresh.Membership.Setoid as MembershipSetoid
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable using (¬?)

open DecSetoid DS using (setoid; _≟_) renaming (Carrier to A)

private
  variable
    r : Level
    R : Rel A r


------------------------------------------------------------------------
-- Re-export contents of Setoid membership
open MembershipSetoid setoid public

------------------------------------------------------------------------
-- Other operations
infix 4 _∈?_ _∉?_

_∈?_ : Decidable (_∈_ {R = R})
x ∈? xs = any? (x ≟_) xs

_∉?_ : Decidable (_∉_ {R = R})
x ∉? xs = ¬? (x ∈? xs)
