------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over semigroups
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semigroup)
open import Relation.Binary.Definitions using (Transitive)

module Algebra.Properties.Semigroup.Divisibility {a ℓ} (S : Semigroup a ℓ) where

open Semigroup S
import Algebra.Divisibility _≈_ _∙_ as Div

------------------------------------------------------------------------
-- Re-export magma divisibility

open import Algebra.Properties.Magma.Divisibility magma public

------------------------------------------------------------------------
-- Additional properties

∣-trans : Transitive _∣_
∣-trans = Div.∣-trans trans ∙-congˡ assoc
