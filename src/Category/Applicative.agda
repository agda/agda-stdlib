------------------------------------------------------------------------
-- The Agda standard library
--
-- Applicative functors
------------------------------------------------------------------------

-- Note that currently the applicative functor laws are not included
-- here.

{-# OPTIONS --without-K --safe #-}

module Category.Applicative where

open import Level using (Level; suc; _⊔_)
open import Data.Unit
open import Category.Applicative.Indexed

private
  variable
    f : Level

RawApplicative : (Set f → Set f) → Set (suc f)
RawApplicative F = RawIApplicative {I = ⊤} λ _ _ → F

module RawApplicative {F : Set f → Set f}
                      (app : RawApplicative F) where
  open RawIApplicative app public

RawApplicativeZero : (Set f → Set f) → Set _
RawApplicativeZero F = RawIApplicativeZero {I = ⊤} (λ _ _ → F)

module RawApplicativeZero {F : Set f → Set f}
                          (app : RawApplicativeZero F) where
  open RawIApplicativeZero app public

RawAlternative : (Set f → Set f) → Set _
RawAlternative F = RawIAlternative {I = ⊤} (λ _ _ → F)

module RawAlternative {F : Set f → Set f}
                      (app : RawAlternative F) where
  open RawIAlternative app public
