------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebra Literals, from a SemiringWithoutAnnihilatingZero
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (SemiringWithoutAnnihilatingZero)

module Algebra.Literals {c ℓ}
  (semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero c ℓ)
  where

open import Algebra.Bundles.Pointed

-- Re-export `Number` instance defined in Algebra.Bundles.Literals

open import Algebra.Bundles.Literals
  (pointedMonoid semiringWithoutAnnihilatingZero) public using (number)
