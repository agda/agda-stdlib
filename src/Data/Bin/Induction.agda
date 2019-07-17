------------------------------------------------------------------------
-- The Agda standard library
--
-- Arranging a well-founded recursion by _<_ on Bin.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Induction where

open import Data.Bin.Base
open import Data.Bin.Properties
open import Data.Bin.Ordering
open import Data.List using (List; []; _∷_; [_])
open import Data.Nat as ℕ using (ℕ)
import Induction.Nat
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Induction.WellFounded using (Acc; module Inverse-image; module Subrelation)
open Acc using (acc)

Acc< =  Acc _<_

<-acc-ℕ :  {n : ℕ} → Acc ℕ._<_ n
-- This means that _<_ is well-founded on ℕ
-- ("each number in ℕ is accessible from 0 by _<_").

<-acc-ℕ {n} = Induction.Nat.<-wellFounded n

-- Derive accessibility for _<_ on Bin from accessibility for _<_ on ℕ:
<ₙon-acc :  ∀ {x} → Acc _<ₙon_ x
<ₙon-acc {x} =  Inverse-image.accessible {_} {_} {_} {Bin} {ℕ} {ℕ._<_} toℕ
                                                     (<-acc-ℕ {toℕ x})

<-acc :  {x : Bin} → Acc< x
<-acc {x} =  Subrelation.accessible {_} {_} {_} {Bin} {_<_} {_<ₙon_} <⇒<ₙon (<ₙon-acc {x})

acc[0] :  Acc< zero
acc[0] =  acc (\x x<0 → contradiction x<0 ≮0)

acc[suc[x]]⇒acc[x] :  ∀ {x} → Acc< (suc x) → Acc< x
acc[suc[x]]⇒acc[x] {x} (acc wf[suc[x]]) =  wf[suc[x]] _ (x<suc[x] x)

acc[double[x]]⇒acc[x] :  ∀ {x} → Acc< (double x) → Acc< x
acc[double[x]]⇒acc[x] {zero}     _            =  acc[0]
acc[double[x]]⇒acc[x] {2[1+ x ]} (acc wf-2x') =  wf-2x' _ (x<double[x] 2[1+ x ] 2[1+x]≢0)
acc[double[x]]⇒acc[x] {1+[2 x ]} (acc wf-2x') =  wf-2x' _ (x<double[x] 1+[2 x ] 1+[2x]≢0)

acc[2[1+x]]⇒acc-suc[x] :  ∀ {x} → Acc _<_ 2[1+ x ] → Acc _<_ (suc x)
acc[2[1+x]]⇒acc-suc[x] {x} acc-2[1+x] =  acc[double[x]]⇒acc[x] {suc x}
                                                                 acc-double-suc-x
  where
  acc-double-suc-x :  Acc _<_ (double (suc x))
  acc-double-suc-x =  subst (Acc _<_) (2[1+-as∘ x) acc-2[1+x]

acc[1+[2x]]⇒acc[x] :  ∀ {x} → Acc< 1+[2 x ] → Acc< x
acc[1+[2x]]⇒acc[x] {x} acc-1+[2x] =  acc[double[x]]⇒acc[x] acc-2x
  where
  acc-suc-2x = subst Acc< (1+[2-as∘ x) acc-1+[2x]
  acc-2x     = acc[suc[x]]⇒acc[x] acc-suc-2x

acc[2[1+x]]⇒acc[1+[2x]] :  ∀ {x} → Acc< 2[1+ x ] → Acc< 1+[2 x ]
acc[2[1+x]]⇒acc[1+[2x]] {x} (acc wf-2[1+x]) =  wf-2[1+x] _ (1+[2x]<2[1+x] x)

------------------------------------------------------------------------------
-- The function  downFrom  below can also serve as an example of usage of Acc.
------------------------------------------------------------------------------

downFrom' : (x : Bin) → Acc _<_ x → List Bin
downFrom' x (acc wf)  with x ≟ zero
... | yes _  =  [ zero ]
... | no x≢0 =  x ∷ (downFrom' (pred x) (wf _ (pred[x]<x {x} x≢0)))

downFrom :  (x : Bin) → List Bin
downFrom x =  downFrom' x <-acc
