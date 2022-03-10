------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of the identity function
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Identity.Effectful {ℓ} where

open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Effect.Comonad
open import Function

Identity : Set ℓ → Set ℓ
Identity A = A

functor : RawFunctor Identity
functor = record
  { _<$>_ = id
  }

applicative : RawApplicative Identity
applicative = record
  { pure = id
  ; _⊛_  = id
  }

monad : RawMonad Identity
monad = record
  { return = id
  ; _>>=_  = _|>′_
  }

comonad : RawComonad Identity
comonad = record
  { extract = id
  ; extend  = id
  }
