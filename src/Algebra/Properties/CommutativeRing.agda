------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Commutative Rings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra using (CommutativeRing)

module Algebra.Properties.CommutativeRing
  {c ℓ} (commutativeRing : CommutativeRing c ℓ) where

open CommutativeRing commutativeRing


------------------------------------------------------------------------
-- Export properties of rings

open import Algebra.Properties.Ring ring public

------------------------------------------------------------------------
-- Properties arising from commutativity

