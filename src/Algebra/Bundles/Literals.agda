------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebra Literals, from a PointedMonoid bundle
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles.Pointed

module Algebra.Bundles.Literals
  {c ℓ} (pointedMonoid : PointedMonoid c ℓ)
  where

open PointedMonoid pointedMonoid

-- Re-export `Number` instance defined in Algebra.Structures.Literals

open import Algebra.Structures.Literals isPointedMonoid public using (number)
