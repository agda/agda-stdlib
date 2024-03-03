------------------------------------------------------------------------
-- The Agda standard library
--
-- Right-biased universe-sensitive functor and monad instances for the
-- Product type.
--
-- To minimize the universe level of the RawFunctor, we require that
-- elements of B are "lifted" to a copy of B at a higher universe level
-- (a ⊔ b). See the Data.Product.Effectful.Examples for how this is
-- done.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra
open import Level

module Data.Product.Effectful.Right
  (a : Level) {b e} (B : RawMonoid b e) where

open import Data.Product.Base
import Data.Product.Effectful.Right.Base as Base
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad; RawMonadT; mkRawMonad)
open import Function.Base using (id; flip; _∘_; _∘′_)
import Function.Identity.Effectful as Id

open RawMonoid B

------------------------------------------------------------------------
-- Re-export the base contents publically

open Base Carrier a public

------------------------------------------------------------------------
-- Basic records

applicative : RawApplicative Productᵣ
applicative = record
  { rawFunctor = functor
  ; pure = _, ε
  ; _<*>_  = zip id _∙_
  }

monad : RawMonad Productᵣ
monad = record
  { rawApplicative = applicative
  ; _>>=_ = uncurry λ a w₁ f → map₂ (w₁ ∙_) (f a)
  }

monadT : RawMonadT (_∘′ Productᵣ)
monadT M = record
  { lift = (_, ε) <$>_
  ; rawMonad = mkRawMonad _
                 (pure ∘′ (_, ε))
                 (λ ma f → ma >>= uncurry λ x b → map₂ (b ∙_) <$> f x)
  } where open RawMonad M

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {F} (App : RawApplicative {a ⊔ b} {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Productᵣ (F A) → F (Productᵣ A)
  sequenceA (fa , y) = (_, y) <$> fa

  mapA : ∀ {A B} → (A → F B) → Productᵣ A → F (Productᵣ B)
  mapA f = sequenceA ∘ map₁ f

  forA : ∀ {A B} → Productᵣ A → (A → F B) → F (Productᵣ B)
  forA = flip mapA

module TraversableM {M} (Mon : RawMonad {a ⊔ b} {a ⊔ b} M) where

  open RawMonad Mon

  open TraversableA rawApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )
