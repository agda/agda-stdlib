------------------------------------------------------------------------
-- The Agda standard library
--
-- Various forms of induction for natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Induction where

open import Function
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _<′_; n<′1+n; <′-step)
open import Data.Nat.Properties using (m<1+n⇒m<n∨m≡n)
open import Data.Product
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic
open import Induction
open import Induction.WellFounded as WF using (WellFounded; WfRec)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Re-export accessability

open WF public using (Acc; acc)

------------------------------------------------------------------------
-- Ordinary induction

Rec : ∀ ℓ → RecStruct ℕ ℓ ℓ
Rec ℓ P zero    = ⊤
Rec ℓ P (suc n) = P n

recBuilder : ∀ {ℓ} → RecursorBuilder (Rec ℓ)
recBuilder P f zero    = _
recBuilder P f (suc n) = f n (recBuilder P f n)

rec : ∀ {ℓ} → Recursor (Rec ℓ)
rec = build recBuilder

------------------------------------------------------------------------
-- Complete induction

CRec : ∀ ℓ → RecStruct ℕ ℓ ℓ
CRec ℓ P zero    = ⊤
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
  <′-wellFounded′ (suc n) n n<′1+n        = <′-wellFounded n
  <′-wellFounded′ (suc n) m (<′-step m<n) = <′-wellFounded′ n m m<n

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

mutual

  <-wellFounded : WellFounded _<_
  <-wellFounded n = acc (<-wellFounded′ n)

  <-wellFounded′ : ∀ n → <-Rec (Acc _<_) n
  <-wellFounded′ zero    y ()
  <-wellFounded′ (suc n) y y<1+n with <-wellFounded n | m<1+n⇒m<n∨m≡n y<1+n
  ... | wfn@(acc rec) | inj₁ y<n  = rec y y<n
  ... | wfn           | inj₂ refl = wfn

-- A version of `<-wellFounded` that cheats by skipping building
-- the first billion proofs. Use this when you require the function
-- using the proof of well-foundedness to evaluate fast.
--
-- IMPORTANT: You have to be a little bit careful when using this to always
-- make the function be strict in some other argument than the accessibility
-- proof, otherwise you will have neutral terms unfolding a billion times
-- before getting stuck.
<-wellFounded-fast : WellFounded _<_
<-wellFounded-fast = <-wellFounded-skip 1000000000
  where
  <-wellFounded-skip : ∀ (k : ℕ) → WellFounded _<_
  <-wellFounded-skip zero    n       = <-wellFounded n
  <-wellFounded-skip (suc k) zero    = <-wellFounded 0
  <-wellFounded-skip (suc k) (suc n) = acc (λ m _ → <-wellFounded-skip k m)

module _ {ℓ} where
  open WF.All <-wellFounded ℓ public
    renaming ( wfRecBuilder to <-recBuilder
             ; wfRec        to <-rec
             )
    hiding (wfRec-builder)

