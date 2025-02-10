------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over semigroups
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Semigroup)

module Algebra.Properties.Semigroup.Divisibility
  {a ℓ} (S : Semigroup a ℓ) where

open import Data.Product.Base using (_,_)
open import Relation.Binary.Definitions using (Transitive)

open Semigroup S

------------------------------------------------------------------------
-- Re-export magma divisibility

open import Algebra.Properties.Magma.Divisibility magma public

------------------------------------------------------------------------
-- Properties of _∣_

∣-trans : Transitive _∣_
∣-trans (p , px≈y) (q , qy≈z) =
  (q ∙ p) , trans (assoc q p _) (trans (∙-congˡ px≈y) qy≈z)

------------------------------------------------------------------------
-- Properties of _∥_

∥-trans : Transitive _∥_
∥-trans (x∣y , y∣x) (y∣z , z∣y) = ∣-trans x∣y y∣z , ∣-trans z∣y y∣x


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.3

∣∣-trans = ∥-trans
{-# WARNING_ON_USAGE ∣∣-trans
"Warning: ∣∣-trans was deprecated in v2.3.
Please use ∥-trans instead. "
#-}
