------------------------------------------------------------------------
-- The Agda standard library
--
-- Induction for _<_ on Bin.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Induction where

open import Data.Bin.Base
open import Data.Bin.Properties
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Induction as ℕ
open import Induction.WellFounded

------------------------------------------------------------------------
-- _<_ is wellFounded

<-wellFounded : WellFounded _<_
<-wellFounded x = Subrelation.accessible <⇒<ℕ toℕ[x]-acc
  where
  toℕ[x]-acc = InverseImage.accessible toℕ (ℕ.<-wellFounded (toℕ x))
