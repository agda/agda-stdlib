------------------------------------------------------------------------
-- The Agda standard library
--
-- Applicative functors
------------------------------------------------------------------------

-- Note that currently the applicative functor laws are not included
-- here.

{-# OPTIONS --without-K --safe #-}

module Category.Applicative where

open import Data.Unit
open import Category.Applicative.Indexed

RawApplicative : ∀ {f} → (Set f → Set f) → Set _
RawApplicative F = RawIApplicative {I = ⊤} (λ _ _ → F)

module RawApplicative {f} {F : Set f → Set f}
                      (app : RawApplicative F) where
  open RawIApplicative app public

RawApplicativeZero : ∀ {f} → (Set f → Set f) → Set _
RawApplicativeZero F = RawIApplicativeZero {I = ⊤} (λ _ _ → F)

module RawApplicativeZero {f} {F : Set f → Set f}
                          (app : RawApplicativeZero F) where
  open RawIApplicativeZero app public

RawAlternative : ∀ {f} → (Set f → Set f) → Set _
RawAlternative F = RawIAlternative {I = ⊤} (λ _ _ → F)

module RawAlternative {f} {F : Set f → Set f}
                          (app : RawAlternative F) where
  open RawIAlternative app public
