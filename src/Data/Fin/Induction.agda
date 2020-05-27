------------------------------------------------------------------------
-- The Agda standard library
--
-- Induction over Fin
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Induction where

open import Data.Fin.Base using (Fin; toℕ; _<_; _≺_)
open import Data.Fin.Properties using (≺⇒<′)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Induction as ℕ
open import Induction
open import Induction.WellFounded as WF
import Relation.Binary.Construct.On as On

------------------------------------------------------------------------
-- Re-export accessability

open WF public using (Acc; acc)

------------------------------------------------------------------------
-- Complete induction for _<_

<-wellFounded : ∀ {n} → WellFounded {A = Fin n} _<_
<-wellFounded = On.wellFounded toℕ ℕ.<-wellFounded

------------------------------------------------------------------------
-- Complete induction for on _≺_

≺-Rec : ∀ {ℓ} → RecStruct ℕ ℓ ℓ
≺-Rec = WfRec _≺_

≺-wellFounded : WellFounded _≺_
≺-wellFounded = Subrelation.wellFounded ≺⇒<′ ℕ.<′-wellFounded

module _ {ℓ} where
  open WF.All ≺-wellFounded ℓ public
    renaming
    ( wfRecBuilder to ≺-recBuilder
    ; wfRec        to ≺-rec
    )
    hiding (wfRec-builder)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

≺-rec-builder    = ≺-recBuilder
{-# WARNING_ON_USAGE ≺-rec-builder
"Warning: ≺-rec-builder was deprecated in v0.15.
Please use ≺-recBuilder instead."
#-}
≺-well-founded   = ≺-wellFounded
{-# WARNING_ON_USAGE ≺-well-founded
"Warning: ≺-well-founded was deprecated in v0.15.
Please use ≺-wellFounded instead."
#-}
