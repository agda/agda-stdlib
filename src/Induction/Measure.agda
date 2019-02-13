------------------------------------------------------------------------
-- The Agda standard library
--
-- well-founded induction by measures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Induction.WellFounded as WF
open import Relation.Binary

module Induction.Measure {a b} {A : Set a} {_≺_ : Rel A a}
               (wf-≺ : WellFounded _≺_)
               {B : Set b} (f : B → A) where

_≺′_ : B → B → Set a
x ≺′ y = f x ≺ f y

acc-≺′ : ∀ x → Acc _≺_ (f x) → Acc _≺′_ x
acc-≺′ x (acc rs) = acc (λ y fy≺fx → acc-≺′ y (rs (f y) fy≺fx))

≺′-wellFounded : WellFounded _≺′_
≺′-wellFounded x = acc-≺′ x (wf-≺ (f x))

open WF.All ≺′-wellFounded b public
  renaming ( wfRecBuilder to ≺′-recBuilder
           ; wfRec        to ≺′-rec
           )
  hiding (wfRec-builder)
