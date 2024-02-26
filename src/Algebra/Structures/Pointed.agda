------------------------------------------------------------------------
-- The Agda standard library
--
-- Defines `IsPointedMonoid`
-- intermediate between `Monoid` and `SemiringWithoutAnnihilatingZero`
--
-- By contrast with the rest of `Algebra.Structures`, this is modelled
-- on an underlying `RawMonoid`, rather than a 'flattened' such signature
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles.Raw
import Algebra.Structures as Structures
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Unit.Base
open import Level using (Level; _⊔_; Lift)

import Algebra.Definitions.RawMonoid as Definitions

module Algebra.Structures.Pointed where

private
  variable
    c ℓ : Level


------------------------------------------------------------------------
-- Structures with 1 binary operation & 2 elements
------------------------------------------------------------------------

record IsPointedMonoid
  (rawMonoid : RawMonoid c ℓ)
  (• : RawMonoid.Carrier rawMonoid) : Set (c ⊔ ℓ)
  where
  open RawMonoid rawMonoid public
  open Structures _≈_

  field
    isMonoid : IsMonoid _∙_ ε

  _×• : ℕ → Carrier
  n ×• = n × • where open Definitions rawMonoid

  module Literals where
    Constraint : ℕ → Set c
    Constraint _ = Lift c ⊤
    fromNat : ∀ n → {{Constraint n}} → Carrier
    fromNat n = n ×•
