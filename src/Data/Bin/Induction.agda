------------------------------------------------------------------------
-- The Agda standard library
--
-- Induction for _<_ on Bin.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Induction where

open import Data.Bin.Base
open import Data.Bin.Properties
open import Data.List using (List; []; _∷_; [_])
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Induction as ℕ
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

------------------------------------------------------------------------
-- _<_ is wellFounded

-- Derived via wellfoundedness of _<_ on ℕ
  
<-wellFounded : WellFounded _<_
<-wellFounded x = Subrelation.accessible <⇒<ℕ toℕ[x]-acc
  where
  toℕ[x]-acc = Inverse-image.accessible toℕ (ℕ.<-wellFounded (toℕ x))

------------------------------------------------------------------------
-- Accessibility

acc[0] :  Acc _<_ zero
acc[0] =  acc (λ x x<0 → contradiction x<0 x≮0)

acc[suc[x]]⇒acc[x] :  ∀ {x} → Acc _<_ (suc x) → Acc _<_ x
acc[suc[x]]⇒acc[x] (acc wf[suc[x]]) =  wf[suc[x]] _ (x<suc[x] _)

acc[double[x]]⇒acc[x] :  ∀ {x} → Acc _<_ (double x) → Acc _<_ x
acc[double[x]]⇒acc[x] {zero}     _            =  acc[0]
acc[double[x]]⇒acc[x] {2[1+ x ]} (acc wf-2x') =  wf-2x' _ (x<double[x] 2[1+ x ] 2[1+x]≢0)
acc[double[x]]⇒acc[x] {1+[2 x ]} (acc wf-2x') =  wf-2x' _ (x<double[x] 1+[2 x ] 1+[2x]≢0)

acc[2[1+x]]⇒acc-suc[x] :  ∀ {x} → Acc _<_ 2[1+ x ] → Acc _<_ (suc x)
acc[2[1+x]]⇒acc-suc[x] {x} acc-2[1+x] =  acc[double[x]]⇒acc[x] {suc x} acc-double-suc-x
  where
  acc-double-suc-x :  Acc _<_ (double (suc x))
  acc-double-suc-x =  subst (Acc _<_) (2[1+_]-double-suc x) acc-2[1+x]

acc[1+[2x]]⇒acc[x] :  ∀ {x} → Acc _<_ 1+[2 x ] → Acc _<_ x
acc[1+[2x]]⇒acc[x] {x} acc-1+[2x] =  acc[double[x]]⇒acc[x] acc-2x
  where
  acc-suc-2x = subst (Acc _<_) (1+[2_]-suc-double x) acc-1+[2x]
  acc-2x     = acc[suc[x]]⇒acc[x] acc-suc-2x

acc[2[1+x]]⇒acc[1+[2x]] :  ∀ {x} → Acc _<_ 2[1+ x ] → Acc _<_ 1+[2 x ]
acc[2[1+x]]⇒acc[1+[2x]] {x} (acc wf-2[1+x]) =  wf-2[1+x] _ (1+[2x]<2[1+x] x)
