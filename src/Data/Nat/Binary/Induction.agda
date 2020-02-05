------------------------------------------------------------------------
-- The Agda standard library
--
-- Induction over _<_ for ℕᵇ.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Binary.Induction where

open import Data.Nat.Binary.Base
open import Data.Nat.Binary.Properties
open import Data.Nat.Base as ℕ using (ℕ)
import Data.Nat.Induction as ℕ
open import Induction.WellFounded

------------------------------------------------------------------------
-- _<_ is wellFounded

<-wellFounded : WellFounded _<_
<-wellFounded x = Subrelation.accessible <⇒<ℕ toℕ[x]-acc
  where
  toℕ[x]-acc = InverseImage.accessible toℕ (ℕ.<-wellFounded (toℕ x))
