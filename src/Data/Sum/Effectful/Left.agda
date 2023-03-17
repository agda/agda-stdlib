------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of the Sum type (Left-biased)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level

module Data.Sum.Effectful.Left {a} (A : Set a) (b : Level) where

open import Data.Sum.Base
open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base

-- To minimize the universe level of the RawFunctor, we require that elements of
-- B are "lifted" to a copy of B at a higher universe level (a ⊔ b). See the
-- examples for how this is done.

------------------------------------------------------------------------
-- Left-biased monad instance for _⊎_

Sumₗ : Set (a ⊔ b) → Set (a ⊔ b)
Sumₗ B = A ⊎ B

functor : RawFunctor Sumₗ
functor = record { _<$>_ = map₂ }

applicative : RawApplicative Sumₗ
applicative = record
  { rawFunctor = functor
  ; pure = inj₂
  ; _<*>_ = [ const ∘ inj₁ , map₂ ]′
  }

empty : A → RawEmpty Sumₗ
empty a = record { empty = inj₁ a }

choice : RawChoice Sumₗ
choice = record { _<|>_ = [ flip const , const ∘ inj₂ ]′ }

applicativeZero : A → RawApplicativeZero Sumₗ
applicativeZero a = record
  { rawApplicative = applicative
  ; rawEmpty = empty a
  }

alternative : A → RawAlternative Sumₗ
alternative a = record
  { rawApplicativeZero = applicativeZero a
  ; rawChoice = choice
  }

monad : RawMonad Sumₗ
monad = record
  { rawApplicative = applicative
  ; _>>=_ = [ const ∘′ inj₁ , _|>′_ ]′
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {F} (App : RawApplicative {a ⊔ b} {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Sumₗ (F A) → F (Sumₗ A)
  sequenceA (inj₁ a) = pure (inj₁ a)
  sequenceA (inj₂ x) = inj₂ <$> x

  mapA : ∀ {A B} → (A → F B) → Sumₗ A → F (Sumₗ B)
  mapA f = sequenceA ∘ map₂ f

  forA : ∀ {A B} → Sumₗ A → (A → F B) → F (Sumₗ B)
  forA = flip mapA

module TraversableM {M} (Mon : RawMonad {a ⊔ b} {a ⊔ b} M) where

  open RawMonad Mon

  open TraversableA rawApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )
