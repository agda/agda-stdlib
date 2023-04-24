------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of the Sum type (Left-biased)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level

module Data.Sum.Effectful.Left.Transformer {a} (A : Set a) (b : Level) where

open import Data.Sum.Base
open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base

private
  variable
    M : Set (a ⊔ b) → Set (a ⊔ b)

-- To minimize the universe level of the RawFunctor, we require that elements of
-- B are "lifted" to a copy of B at a higher universe level (a ⊔ b). See the
-- examples for how this is done.

open import Data.Sum.Effectful.Left A b using (Sumₗ)

------------------------------------------------------------------------
-- Left-biased monad transformer instance for _⊎_

record SumₗT
         (M : Set (a ⊔ b) → Set (a ⊔ b))
         (B : Set (a ⊔ b)) : Set (a ⊔ b) where
  constructor mkSumₗT
  field runSumₗT : M (Sumₗ B)
open SumₗT public

------------------------------------------------------------------------
-- Structure

functor : RawFunctor M → RawFunctor (SumₗT M)
functor M = record
  { _<$>_ = λ f → mkSumₗT ∘′ (map₂ f <$>_) ∘′ runSumₗT
  } where open RawFunctor M

applicative : RawApplicative M → RawApplicative (SumₗT M)
applicative M = record
  { rawFunctor = functor rawFunctor
  ; pure = mkSumₗT ∘′ pure ∘′ inj₂
  ; _<*>_ = λ mf mx → mkSumₗT ([ const ∘′ inj₁ , map₂ ]′ <$> runSumₗT mf <*> runSumₗT mx)
  } where open RawApplicative M

empty : RawApplicative M → A → RawEmpty (SumₗT M)
empty M a = record
  { empty = mkSumₗT (pure (inj₁ a))
  } where open RawApplicative M

choice : RawApplicative M → RawChoice (SumₗT M)
choice M = record
  { _<|>_ = λ ma₁ ma₂ → mkSumₗT ([ flip const , const ∘ inj₂ ]′ <$> runSumₗT ma₁ <*> runSumₗT ma₂)
  } where open RawApplicative M

applicativeZero : RawApplicative M → A → RawApplicativeZero (SumₗT M)
applicativeZero M a = record
  { rawApplicative = applicative M
  ; rawEmpty = empty M a
  }

alternative : RawApplicative M → A → RawAlternative (SumₗT M)
alternative M a = record
  { rawApplicativeZero = applicativeZero M a
  ; rawChoice = choice M
  }

monad : RawMonad M → RawMonad (SumₗT M)
monad M = record
  { rawApplicative = applicative rawApplicative
  ; _>>=_ = λ ma f → mkSumₗT $ do
                       a ← runSumₗT ma
                       [ pure ∘′ inj₁ , runSumₗT ∘′ f ]′ a
  } where open RawMonad M

monadT : RawMonadT SumₗT
monadT M = record
  { lift = mkSumₗT ∘′ (inj₂ <$>_)
  ; rawMonad = monad M
  } where open RawMonad M
