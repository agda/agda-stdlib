------------------------------------------------------------------------
-- The Agda standard library
--
-- The state monad transformer
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level

module Effect.Monad.State.Transformer where

open import Data.Product using (_×_; _,_; map₂; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base
open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base

private
  variable
    ℓ f s : Level
    A B I : Set ℓ
    S S₁ S₂ : Set s
    M : Set s → Set f

------------------------------------------------------------------------
-- State monad operations

record RawMonadState
       (S : Set s)
       (M : Set s → Set f)
       : Set (suc s ⊔ f) where
  field
    get : M S
    put : S → M ⊤
    modify : (S → S) → M ⊤

------------------------------------------------------------------------
-- State monad transformer

record StateT
       (S : Set s)
       (M : Set s → Set f)
       (A : Set s)
       : Set (s ⊔ f) where
  constructor mkStateT
  field runStateT : S → M (S × A)
open StateT public

evalStateT : RawFunctor M → StateT S M A → S → M A
evalStateT M ma s = let open RawFunctor M in proj₂ <$> runStateT ma s

execStateT : RawFunctor M → StateT S M A → S → M S
execStateT M ma s = let open RawFunctor M in proj₁ <$> runStateT ma s

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
  ; _>>=_ = λ ma f → mkStateT $ λ r →
              do (s , a) ← StateT.runStateT ma r
                 StateT.runStateT (f a) r
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
  { get = mkStateT (λ s → pure (s , s))
  ; put = λ s → mkStateT (λ _ → pure (s , _))
  ; modify = λ f → mkStateT (λ s → pure (f s , _))
  } where open RawMonad M

LiftMonadState : RawMonad M →
                 RawMonadState S₁ M →
                 RawMonadState S₁ (StateT S₂ M)
LiftMonadState M Mon = record
  { get     = mkStateT (λ s₂ → get >>= λ s₁ → pure (s₂ , s₁))
  ; put    = λ s₁ → mkStateT (λ s₂ → (s₂ , _) <$ put s₁)
  ; modify = λ f₁ → mkStateT (λ s₂ → (s₂ ,_) <$> modify f₁)
  }
  where open RawMonad M; open RawMonadState Mon
