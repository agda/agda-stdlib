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
open import Induction.WellFounded as WFI
import Relation.Binary.Construct.On as On

------------------------------------------------------------------------
-- Re-export Acc and acc

open WFI public using (Acc; acc)

------------------------------------------------------------------------
-- _<_ is wellFounded

<-wellFounded : WellFounded _<_
<-wellFounded = Subrelation.wellFounded <⇒<ℕ
  (On.wellFounded toℕ ℕ.<-wellFounded)
