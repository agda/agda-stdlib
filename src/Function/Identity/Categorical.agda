------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of the identity function
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Category.Comonad
open import Function
open import Level

module Function.Identity.Categorical {ℓ : Level} where

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
