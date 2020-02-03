------------------------------------------------------------------------
-- The Agda standard library
--
-- Various forms of induction for natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Induction where

open import Function
open import Data.Nat.Base
open import Data.Nat.Properties using (≤⇒≤′)
open import Data.Product
open import Data.Unit
open import Induction
open import Induction.WellFounded as WF
open import Level using (Lift)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

------------------------------------------------------------------------
-- Re-export accessability

open WF public using (Acc; acc)

------------------------------------------------------------------------
-- Ordinary induction

Rec : ∀ ℓ → RecStruct ℕ ℓ ℓ
Rec ℓ P zero    = Lift ℓ ⊤
Rec ℓ P (suc n) = P n

recBuilder : ∀ {ℓ} → RecursorBuilder (Rec ℓ)
recBuilder P f zero    = _
recBuilder P f (suc n) = f n (recBuilder P f n)

rec : ∀ {ℓ} → Recursor (Rec ℓ)
rec = build recBuilder

------------------------------------------------------------------------
-- Complete induction

CRec : ∀ ℓ → RecStruct ℕ ℓ ℓ
CRec ℓ P zero    = Lift ℓ ⊤
CRec ℓ P (suc n) = P n × CRec ℓ P n

cRecBuilder : ∀ {ℓ} → RecursorBuilder (CRec ℓ)
cRecBuilder P f zero    = _
cRecBuilder P f (suc n) = f n ih , ih
  where ih = cRecBuilder P f n

cRec : ∀ {ℓ} → Recursor (CRec ℓ)
cRec = build cRecBuilder

------------------------------------------------------------------------
-- Complete induction based on _<′_

<′-Rec : ∀ {ℓ} → RecStruct ℕ ℓ ℓ
<′-Rec = WfRec _<′_

mutual

  <′-wellFounded : WellFounded _<′_
  <′-wellFounded n = acc (<′-wellFounded′ n)

  <′-wellFounded′ : ∀ n → <′-Rec (Acc _<′_) n
  <′-wellFounded′ (suc n) .n ≤′-refl       = <′-wellFounded n
  <′-wellFounded′ (suc n)  m (≤′-step m<n) = <′-wellFounded′ n m m<n

module _ {ℓ} where
  open WF.All <′-wellFounded ℓ public
    renaming ( wfRecBuilder to <′-recBuilder
             ; wfRec        to <′-rec
             )
    hiding (wfRec-builder)

------------------------------------------------------------------------
-- Complete induction based on _<_

<-Rec : ∀ {ℓ} → RecStruct ℕ ℓ ℓ
<-Rec = WfRec _<_

<-wellFounded : WellFounded _<_
<-wellFounded = Subrelation.wellFounded ≤⇒≤′ <′-wellFounded

module _ {ℓ} where
  open WF.All <-wellFounded ℓ public
    renaming ( wfRecBuilder to <-recBuilder
             ; wfRec        to <-rec
             )
    hiding (wfRec-builder)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

rec-builder      = recBuilder
{-# WARNING_ON_USAGE rec-builder
"Warning: rec-builder was deprecated in v0.15.
Please use recBuilder instead."
#-}
cRec-builder     = cRecBuilder
{-# WARNING_ON_USAGE cRec-builder
"Warning: cRec-builder was deprecated in v0.15.
Please use cRecBuilder instead."
#-}
<′-rec-builder   = <′-recBuilder
{-# WARNING_ON_USAGE <′-rec-builder
"Warning: <′-rec-builder was deprecated in v0.15.
Please use <′-recBuilder instead."
#-}
<-rec-builder    = <-recBuilder
{-# WARNING_ON_USAGE <-rec-builder
"Warning: <-rec-builder was deprecated in v0.15.
Please use <-recBuilder instead."
#-}
<′-well-founded  = <′-wellFounded
{-# WARNING_ON_USAGE <′-well-founded
"Warning: <′-well-founded was deprecated in v0.15.
Please use <′-wellFounded instead."
#-}
<′-well-founded′ = <′-wellFounded′
{-# WARNING_ON_USAGE <′-well-founded′
"Warning: <′-well-founded′ was deprecated in v0.15.
Please use <′-wellFounded′ instead."
#-}
<-well-founded   = <-wellFounded
{-# WARNING_ON_USAGE <-well-founded
"Warning: <-well-founded was deprecated in v0.15.
Please use <-wellFounded instead."
#-}
