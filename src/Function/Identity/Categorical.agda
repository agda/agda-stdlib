------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of the identity function
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Identity.Categorical {ℓ} where

open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Category.Monad.Indexed
open import Category.Comonad
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

monadT-identity : ∀ {T} → RawIMonadT T → RawIMonad (T (λ _ _ → Identity))
monadT-identity M = RawIMonadT.rawIMonadT M monad
