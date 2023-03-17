------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of the Sum type (Right-biased)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level

module Data.Sum.Effectful.Right.Transformer (a : Level) {b} (B : Set b) where

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

open import Data.Sum.Effectful.Right a B using (Sumᵣ)

------------------------------------------------------------------------
-- Right-biased monad transformer instance for _⊎_

record SumᵣT
         (M : Set (a ⊔ b) → Set (a ⊔ b))
         (B : Set (a ⊔ b)) : Set (a ⊔ b) where
  constructor mkSumᵣT
  field runSumᵣT : M (Sumᵣ B)
open SumᵣT public

------------------------------------------------------------------------
-- Structure

functor : RawFunctor M → RawFunctor (SumᵣT M)
functor M = record
  { _<$>_ = λ f → mkSumᵣT ∘′ (map₁ f <$>_) ∘′ runSumᵣT
  } where open RawFunctor M

applicative : RawApplicative M → RawApplicative (SumᵣT M)
applicative M = record
  { rawFunctor = functor rawFunctor
  ; pure = mkSumᵣT ∘′ pure ∘′ inj₁
  ; _<*>_ = λ mf mx → mkSumᵣT ([ map₁ , const ∘′ inj₂ ]′ <$> runSumᵣT mf <*> runSumᵣT mx)
  } where open RawApplicative M

empty : RawApplicative M → B → RawEmpty (SumᵣT M)
empty M a = record
  { empty = mkSumᵣT (pure (inj₂ a))
  } where open RawApplicative M

choice : RawApplicative M → RawChoice (SumᵣT M)
choice M = record
  { _<|>_ = λ ma₁ ma₁ → mkSumᵣT ([ const ∘ inj₁ , flip const ]′ <$> runSumᵣT ma₁ <*> runSumᵣT ma₁)
  } where open RawApplicative M

applicativeZero : RawApplicative M → B → RawApplicativeZero (SumᵣT M)
applicativeZero M a = record
  { rawApplicative = applicative M
  ; rawEmpty = empty M a
  }

alternative : RawApplicative M → B → RawAlternative (SumᵣT M)
alternative M a = record
  { rawApplicativeZero = applicativeZero M a
  ; rawChoice = choice M
  }

monad : RawMonad M → RawMonad (SumᵣT M)
monad M = record
  { rawApplicative = applicative rawApplicative
  ; _>>=_ = λ ma f → mkSumᵣT $ do
                       a ← runSumᵣT ma
                       [ runSumᵣT ∘′ f , pure ∘′ inj₂ ]′ a
  } where open RawMonad M

monadT : RawMonadT SumᵣT
monadT M = record
  { lift = mkSumᵣT ∘′ (inj₁ <$>_)
  ; rawMonad = monad M
  } where open RawMonad M
