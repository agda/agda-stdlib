------------------------------------------------------------------------
-- The Agda standard library
--
-- The reader monad transformer
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level

module Effect.Monad.Reader.Transformer {r} (R : Set r) (a : Level) where

open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base

private
  variable
    ℓ : Level
    A B I : Set ℓ
    M : Set (r ⊔ a) → Set (r ⊔ a)

------------------------------------------------------------------------
-- Reader monad operations

record RawMonadReader
       (M : Set (r ⊔ a) → Set (r ⊔ a))
       : Set (suc (r ⊔ a)) where
  field
    rawMonad : RawMonad M
    reader : (R → A) → M A
    local  : (R → R) → M A → M A

  open RawMonad rawMonad public

  ask : M (Lift a R)
  ask = reader lift

------------------------------------------------------------------------
-- Reader monad transformer

record ReaderT
       (M : Set (r ⊔ a) → Set (r ⊔ a))
       (A : Set (r ⊔ a))
       : Set (r ⊔ a) where
  constructor mkReaderT
  field runReaderT : R → M A

------------------------------------------------------------------------
-- Structure

functor : RawFunctor M → RawFunctor (ReaderT M)
functor M = record
  { _<$>_ = λ f ma → mkReaderT (λ r → f <$> ReaderT.runReaderT ma r)
  } where open RawFunctor M

applicative : RawApplicative M → RawApplicative (ReaderT M)
applicative M = record
  { rawFunctor = functor rawFunctor
  ; pure = mkReaderT ∘′ const ∘′ pure
  ; _<*>_ = λ mf mx → mkReaderT (λ r → ReaderT.runReaderT mf r <*> ReaderT.runReaderT mx r)
  } where open RawApplicative M

empty : RawEmpty M → RawEmpty (ReaderT M)
empty M = record
  { empty = mkReaderT (const (RawEmpty.empty M))
  }

choice : RawChoice M → RawChoice (ReaderT M)
choice M = record
  { _<|>_ = λ ma₁ ma₂ → mkReaderT $ λ r →
            ReaderT.runReaderT ma₁ r
            <|> ReaderT.runReaderT ma₂ r
  } where open RawChoice M

applicativeZero : RawApplicativeZero M → RawApplicativeZero (ReaderT M)
applicativeZero M = record
  { rawApplicative = applicative rawApplicative
  ; rawEmpty = empty rawEmpty
  } where open RawApplicativeZero M

alternative : RawAlternative M → RawAlternative (ReaderT M)
alternative M = record
  { rawApplicativeZero = applicativeZero rawApplicativeZero
  ; rawChoice = choice rawChoice
  } where open RawAlternative M

monad : RawMonad M → RawMonad (ReaderT M)
monad M = record
  { rawApplicative = applicative rawApplicative
  ; _>>=_ = λ ma f → mkReaderT $ λ r →
              do a ← ReaderT.runReaderT ma r
                 ReaderT.runReaderT (f a) r
  } where open RawMonad M

monadZero : RawMonadZero M → RawMonadZero (ReaderT M)
monadZero M = record
  { rawMonad = monad (RawMonadZero.rawMonad M)
  ; rawEmpty = empty (RawMonadZero.rawEmpty M)
  }

monadPlus : RawMonadPlus M → RawMonadPlus (ReaderT M)
monadPlus M = record
  { rawMonadZero = monadZero rawMonadZero
  ; rawChoice = choice rawChoice
  } where open RawMonadPlus M

------------------------------------------------------------------------
-- Monad reader transformer specifics

monadT : RawMonadT ReaderT
monadT M = record
  { lift = mkReaderT ∘′ const
  ; rawMonad = monad M
  }

monadReader : RawMonad M → RawMonadReader (ReaderT M)
monadReader M = record
  { rawMonad = monad M
  ; reader = λ f → mkReaderT (pure ∘′ f)
  ; local = λ f ma → mkReaderT (ReaderT.runReaderT ma ∘′ f)
  } where open RawMonad M
