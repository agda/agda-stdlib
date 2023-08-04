------------------------------------------------------------------------
-- The Agda standard library
--
-- The state monad transformer
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (Level; suc; _⊔_)

module Effect.Monad.State.Transformer where

open import Algebra using (RawMonoid)
open import Data.Product using (_×_; _,_; map₂; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base
open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base

open import Effect.Monad.Reader.Transformer using (RawMonadReader)

private
  variable
    f s : Level
    A B : Set s
    S S₁ S₂ : Set s
    M : Set s → Set f

------------------------------------------------------------------------
-- Re-export the basic type and definitions

open import Effect.Monad.State.Transformer.Base public
  using ( RawMonadState
        ; StateT
        ; mkStateT
        ; runStateT
        ; evalStateT
        ; execStateT
        )

------------------------------------------------------------------------
-- Structure

functor : RawFunctor M → RawFunctor (StateT S M)
functor M = record
  { _<$>_ = λ f ma → mkStateT (λ s → map₂ f <$> StateT.runStateT ma s)
  } where open RawFunctor M

applicative : RawMonad M → RawApplicative (StateT S M)
applicative M = record
  { rawFunctor = functor rawFunctor
  ; pure = λ a → mkStateT (pure ∘′ (_, a))
  ; _<*>_ = λ mf mx → mkStateT $ λ s →
              do (s , f) ← StateT.runStateT mf s
                 (s , x) ← StateT.runStateT mx s
                 pure (s , f x)
  } where open RawMonad M

empty : RawEmpty M → RawEmpty (StateT S M)
empty M = record
  { empty = mkStateT (const (RawEmpty.empty M))
  }

choice : RawChoice M → RawChoice (StateT S M)
choice M = record
  { _<|>_ = λ ma₁ ma₂ → mkStateT $ λ s →
            StateT.runStateT ma₁ s
            <|> StateT.runStateT ma₂ s
  } where open RawChoice M

applicativeZero : RawMonadZero M → RawApplicativeZero (StateT S M)
applicativeZero M = record
  { rawApplicative = applicative (RawMonadZero.rawMonad M)
  ; rawEmpty = empty (RawMonadZero.rawEmpty M)
  }

alternative : RawMonadPlus M → RawAlternative (StateT S M)
alternative M = record
  { rawApplicativeZero = applicativeZero rawMonadZero
  ; rawChoice = choice rawChoice
  } where open RawMonadPlus M

monad : RawMonad M → RawMonad (StateT S M)
monad M = record
  { rawApplicative = applicative M
  ; _>>=_ = λ ma f → mkStateT $ λ s →
              do (s , a) ← StateT.runStateT ma s
                 StateT.runStateT (f a) s
  } where open RawMonad M

monadZero : RawMonadZero M → RawMonadZero (StateT S M)
monadZero M = record
  { rawMonad = monad (RawMonadZero.rawMonad M)
  ; rawEmpty = empty (RawMonadZero.rawEmpty M)
  }

monadPlus : RawMonadPlus M → RawMonadPlus (StateT S M)
monadPlus M = record
  { rawMonadZero = monadZero rawMonadZero
  ; rawChoice = choice rawChoice
  } where open RawMonadPlus M

------------------------------------------------------------------------
-- State monad transformer specifics

monadT : RawMonadT {f = s} {g₁ = f} {g₂ = s ⊔ f} (StateT S)
monadT M = record
  { lift = λ ma → mkStateT (λ s → (s ,_) <$> ma)
  ; rawMonad = monad M
  } where open RawMonad M

monadState : RawMonad M → RawMonadState S (StateT S M)
monadState M = record
  { gets   = λ f → mkStateT (λ s → pure (s , f s))
  ; modify = λ f → mkStateT (λ s → pure (f s , _))
  } where open RawMonad M

------------------------------------------------------------------------
-- State monad transformer specifics

liftStateT : RawMonad M →
             RawMonadState S₁ M →
             RawMonadState S₁ (StateT S₂ M)
liftStateT M Mon = record
  { gets   = λ f₁ → lift (gets f₁)
  ; modify = λ f₁ → lift (modify f₁)
  } where open RawMonadTd (monadT M) using (lift); open RawMonadState Mon

open import Effect.Monad.Reader.Transformer.Base

liftReaderT : RawMonadState S₁ M →
              RawMonadState S₁ (ReaderT S₂ M)
liftReaderT Mon = record
  { gets   = λ f → mkReaderT (const (gets f))
  ; modify = λ f → mkReaderT (const (modify f))
  } where open RawMonadState Mon

open import Effect.Monad.Writer.Transformer.Base

liftWriterT : (MS : RawMonoid s f) →
              RawFunctor M →
              RawMonadState S M →
              RawMonadState S (WriterT MS M)
liftWriterT MS M Mon = record
  { gets   = λ f → mkWriterT λ w → (gets ((w ,_) ∘′ f))
  ; modify = λ f → mkWriterT λ w → (const (w , tt) <$> modify f)
  } where open RawMonadState Mon
          open RawFunctor M
