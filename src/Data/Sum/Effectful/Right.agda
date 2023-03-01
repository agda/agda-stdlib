------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of the Sum type (Right-biased)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level

module Data.Sum.Effectful.Right (a : Level) {b} (B : Set b) where

open import Algebra.Bundles using (RawMonoid)
open import Data.Sum.Base
open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base

Sumᵣ : Set (a ⊔ b) → Set (a ⊔ b)
Sumᵣ A = A ⊎ B

functor : RawFunctor Sumᵣ
functor = record { _<$>_ = map₁ }

empty : B → RawEmpty Sumᵣ
empty b = record { empty = inj₂ b }

choice : RawChoice Sumᵣ
choice = record { _<|>_ = [ const ∘′ inj₁ , flip const ]′ }

applicative : RawApplicative Sumᵣ
applicative = record
  { rawFunctor = functor
  ; pure = inj₁
  ; _<*>_ = [ map₁ , const ∘ inj₂ ]′
  }

applicativeZero : B → RawApplicativeZero Sumᵣ
applicativeZero b = record
  { rawApplicative = applicative
  ; rawEmpty = empty b
  }

alternative : B → RawAlternative Sumᵣ
alternative b = record
  { rawApplicativeZero = applicativeZero b
  ; rawChoice = choice
  }

monad : RawMonad Sumᵣ
monad = record
  { rawApplicative = applicative
  ; _>>=_ = [ _|>′_ , const ∘′ inj₂ ]′
  }

monadZero : B → RawMonadZero Sumᵣ
monadZero b = record
  { rawMonad = monad
  ; rawEmpty = empty b
  }

monadPlus : B → RawMonadPlus Sumᵣ
monadPlus b = record
  { rawMonadZero = monadZero b
  ; rawChoice = choice
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {F} (App : RawApplicative {a ⊔ b} {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Sumᵣ (F A) → F (Sumᵣ A)
  sequenceA (inj₂ a) = pure (inj₂ a)
  sequenceA (inj₁ x) = inj₁ <$> x

  mapA : ∀ {A B} → (A → F B) → Sumᵣ A → F (Sumᵣ B)
  mapA f = sequenceA ∘ map₁ f

  forA : ∀ {A B} → Sumᵣ A → (A → F B) → F (Sumᵣ B)
  forA = flip mapA

module TraversableM {M} (Mon : RawMonad {a ⊔ b} {a ⊔ b} M) where

  open RawMonad Mon

  open TraversableA rawApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )
