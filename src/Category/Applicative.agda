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
open import Data.Unit.Polymorphic
open import Category.Applicative.Indexed

private
  variable
    f : Level

RawApplicative : (Set f → Set f) → Set (suc f)
RawApplicative {i} F = RawIApplicative {I = ⊤ {i}} λ _ _ → F

module RawApplicative {F : Set f → Set f}
                      (app : RawApplicative F) where
  open RawIApplicative app public

RawApplicativeZero : (Set f → Set f) → Set _
RawApplicativeZero {i} F = RawIApplicativeZero {I = ⊤ {i}} (λ _ _ → F)

module RawApplicativeZero {F : Set f → Set f}
                          (app : RawApplicativeZero F) where
  open RawIApplicativeZero app public

RawAlternative : (Set f → Set f) → Set _
RawAlternative {i} F = RawIAlternative {I = ⊤ {i}} (λ _ _ → F)

module RawAlternative {F : Set f → Set f}
                      (app : RawAlternative F) where
  open RawIAlternative app public
