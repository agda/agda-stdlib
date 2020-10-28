------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over commutative semigroups
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeSemigroup)

module Algebra.Properties.CommutativeSemigroup.Divisibility
  {a ℓ} (CM : CommutativeSemigroup a ℓ)
  where

open CommutativeSemigroup CM

------------------------------------------------------------------------------
-- Re-export the contents of divisibility over semigroups

open import Algebra.Properties.Semigroup.Divisibility semigroup public

------------------------------------------------------------------------------
-- Re-export the contents of divisibility over commutative magmas

open import Algebra.Properties.CommutativeMagma.Divisibility commutativeMagma public
  using (x∣xy; xy≈z⇒x∣z; ∣-factors; ∣-factors-≈)
