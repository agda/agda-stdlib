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
-- Properties of _∣ʳ_

x∣ʳy⇒xz∣ʳyz : ∀ {x y} z → x ∣ʳ y → x ∙ z ∣ʳ y ∙ z
x∣ʳy⇒xz∣ʳyz z (p , px≈y) = p , trans (sym (assoc p _ z)) (∙-congʳ px≈y)

∣ʳ-trans : Transitive _∣ʳ_
∣ʳ-trans (p , px≈y) (q , qy≈z) =
  q ∙ p , trans (assoc q p _) (trans (∙-congˡ px≈y) qy≈z)

------------------------------------------------------------------------
-- Properties of _∣ˡ__

x∣ˡy⇒zx∣ˡzy : ∀ {x y} z → x ∣ˡ y → z ∙ x ∣ˡ z ∙ y
x∣ˡy⇒zx∣ˡzy z (p , xp≈y) = p , trans (assoc z _ p) (∙-congˡ xp≈y)

∣ˡ-trans : Transitive _∣ˡ_
∣ˡ-trans (p , xp≈y) (q , yq≈z) =
  p ∙ q , trans (sym (assoc _ p q)) (trans (∙-congʳ xp≈y) yq≈z)

------------------------------------------------------------------------
-- Properties of _∥_

∥-trans : Transitive _∥_
∥-trans (x∣y , y∣x) (y∣z , z∣y) = ∣ʳ-trans x∣y y∣z , ∣ʳ-trans z∣y y∣x


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

∣-trans = ∣ʳ-trans
{-# WARNING_ON_USAGE ∣-trans
"Warning: ∣-trans was deprecated in v2.3.
Please use ∣ʳ-trans instead. "
#-}
