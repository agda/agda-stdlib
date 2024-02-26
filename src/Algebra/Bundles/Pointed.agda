------------------------------------------------------------------------
-- The Agda standard library
--
-- `Pointed` intermediate between `Monoid` and `SemiringWithoutAnnihilatingZero`
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles
open import Algebra.Bundles.Raw
open import Algebra.Core
open import Algebra.Structures.Pointed as Pointed using (IsPointedMonoid)
import Algebra.Properties.Monoid.Mult as Mult
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Unit.Base
open import Level using (Level; suc; _⊔_; Lift)
open import Relation.Binary.Core using (Rel)

module Algebra.Bundles.Pointed where

private
  variable
    c ℓ : Level

------------------------------------------------------------------------
-- Bundles with 1 binary operation & 2 elements
------------------------------------------------------------------------

record PointedMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    rawMonoid  : RawMonoid c ℓ
  open RawMonoid rawMonoid using (Carrier)
  field
    •      : Carrier
    isPointedMonoid : IsPointedMonoid rawMonoid •

  open IsPointedMonoid isPointedMonoid public

------------------------------------------------------------------------
-- instance from any SemiringWithoutAnnihilatingZero

pointedMonoid : SemiringWithoutAnnihilatingZero c ℓ → PointedMonoid c ℓ
pointedMonoid semiringWithoutAnnihilatingZero
  = record { isPointedMonoid = isPointedMonoid }
  where
  open SemiringWithoutAnnihilatingZero semiringWithoutAnnihilatingZero
    using (1#; +-rawMonoid; +-isMonoid)
  isPointedMonoid : IsPointedMonoid +-rawMonoid 1#
  isPointedMonoid = record { isMonoid = +-isMonoid }

