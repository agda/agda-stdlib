------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over semigroups
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semigroup)
open import Data.Product using (_,_)
open import Relation.Binary.Definitions using (Transitive)

module Algebra.Properties.Semigroup.Divisibility
  {a ℓ} (S : Semigroup a ℓ) where

open Semigroup S

------------------------------------------------------------------------
-- Re-export magma divisibility

open import Algebra.Properties.Magma.Divisibility magma public

------------------------------------------------------------------------
-- Additional properties

∣-trans : Transitive _∣_
∣-trans (p , px≈y) (q , qy≈z) =
  q ∙ p , trans (assoc q p _) (trans (∙-congˡ px≈y) qy≈z)
