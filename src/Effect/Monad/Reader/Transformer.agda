------------------------------------------------------------------------
-- The Agda standard library
--
-- The reader monad transformer
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}


module Effect.Monad.Reader.Transformer where

open import Algebra using (RawMonoid)
open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base using (_∘′_; const; _$_)
open import Level using (Level; _⊔_)

private
  variable
    r g g₁ g₂ : Level
    R R₁ R₂ : Set r
    A B : Set r
    M : Set r → Set g

------------------------------------------------------------------------
-- Re-export the basic type definitions

open import Effect.Monad.Reader.Transformer.Base public
  using ( RawMonadReader
        ; ReaderT
        ; mkReaderT
        ; runReaderT
        )

------------------------------------------------------------------------
-- Structure

functor : RawFunctor M → RawFunctor (ReaderT R M)
functor M = record
  { _<$>_ = λ f ma → mkReaderT (λ r → f <$> ReaderT.runReaderT ma r)
  } where open RawFunctor M

applicative : RawApplicative M → RawApplicative (ReaderT R M)
applicative M = record
  { rawFunctor = functor rawFunctor
  ; pure = mkReaderT ∘′ const ∘′ pure
  ; _<*>_ = λ mf mx → mkReaderT (λ r → ReaderT.runReaderT mf r <*> ReaderT.runReaderT mx r)
  } where open RawApplicative M

empty : RawEmpty M → RawEmpty (ReaderT R M)
empty M = record
  { empty = mkReaderT (const (RawEmpty.empty M))
  }

choice : RawChoice M → RawChoice (ReaderT R M)
choice M = record
  { _<|>_ = λ ma₁ ma₂ → mkReaderT $ λ r →
            ReaderT.runReaderT ma₁ r
            <|> ReaderT.runReaderT ma₂ r
  } where open RawChoice M

applicativeZero : RawApplicativeZero M → RawApplicativeZero (ReaderT R M)
applicativeZero M = record
  { rawApplicative = applicative rawApplicative
  ; rawEmpty = empty rawEmpty
  } where open RawApplicativeZero M using (rawApplicative; rawEmpty)

alternative : RawAlternative M → RawAlternative (ReaderT R M)
alternative M = record
  { rawApplicativeZero = applicativeZero rawApplicativeZero
  ; rawChoice = choice rawChoice
  } where open RawAlternative M

monad : RawMonad M → RawMonad (ReaderT R M)
monad M = record
  { rawApplicative = applicative rawApplicative
  ; _>>=_ = λ ma f → mkReaderT $ λ r →
              do a ← ReaderT.runReaderT ma r
                 ReaderT.runReaderT (f a) r
  } where open RawMonad M

monadZero : RawMonadZero M → RawMonadZero (ReaderT R M)
monadZero M = record
  { rawMonad = monad (RawMonadZero.rawMonad M)
  ; rawEmpty = empty (RawMonadZero.rawEmpty M)
  }

monadPlus : RawMonadPlus M → RawMonadPlus (ReaderT R M)
monadPlus M = record
  { rawMonadZero = monadZero rawMonadZero
  ; rawChoice = choice rawChoice
  } where open RawMonadPlus M

------------------------------------------------------------------------
-- Monad reader transformer specifics

monadT : RawMonadT {g₁ = g₁} {g₂ = r ⊔ g₁} (ReaderT {r} R)
monadT M = record
  { lift = mkReaderT ∘′ const
  ; rawMonad = monad M
  }

monadReader : RawMonad M → RawMonadReader R (ReaderT R M)
monadReader M = record
  { reader = λ f → mkReaderT (pure ∘′ f)
  ; local = λ f ma → mkReaderT (ReaderT.runReaderT ma ∘′ f)
  } where open RawMonad M

liftReaderT : RawMonadReader R₁ M →
              RawMonadReader R₁ (ReaderT R₂ M)
liftReaderT MRead = record
  { reader = λ k → mkReaderT (const (reader k))
  ; local = λ f mx → mkReaderT (λ r₂ → local f (runReaderT mx r₂))
  } where open RawMonadReader MRead

open import Data.Product using (_×_; _,_)
open import Effect.Monad.Writer.Transformer.Base

liftWriterT : (MR : RawMonoid r g) →
              RawFunctor M →
              RawMonadReader R M →
              RawMonadReader R (WriterT MR M)
liftWriterT MR M MRead = record
  { reader = λ k → mkWriterT λ w → ((w ,_) <$> reader k)
  ; local = λ f mx → mkWriterT λ w → (local f (runWriterT mx w))
  } where open RawMonadReader MRead
          open RawFunctor M

open import Effect.Monad.State.Transformer.Base

liftStateT : RawFunctor M →
             RawMonadReader R₁ M →
             RawMonadReader R₁ (StateT R₂ M)
liftStateT M MRead = record
  { reader = λ k → mkStateT (λ s → (s ,_) <$> reader k)
  ; local = λ f mx → mkStateT (λ s → local f (runStateT mx s))
  } where open RawMonadReader MRead
          open RawFunctor M
