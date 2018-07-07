------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of List⁺
------------------------------------------------------------------------

module Data.List.NonEmpty.Categorical where

import Data.List.Categorical as List
open import Data.List.NonEmpty
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Category.Monad.Identity
open import Function

------------------------------------------------------------------------
-- List⁺ applicative functor

functor : ∀ {f} → RawFunctor {f} List⁺
functor = record
  { _<$>_ = map
  }

applicative : ∀ {f} → RawApplicative {f} List⁺
applicative = record
  { pure = [_]
  ; _⊛_  = λ fs as → concatMap (λ f → map f as) fs
  }

------------------------------------------------------------------------
-- List⁺ monad

monad : ∀ {f} → RawMonad {f} List⁺
monad = record
  { return = [_]
  ; _>>=_  = flip concatMap
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

private
 module Monadic {m} {M : Set m → Set m} (Mon : RawMonad M) where

  open RawMonad Mon

  sequence : ∀ {A} → List⁺ (M A) → M (List⁺ A)
  sequence (x ∷ xs) = _∷_ <$> x ⊛ List.sequence Mon xs

  mapM : ∀ {a} {A : Set a} {B} → (A → M B) → List⁺ A → M (List⁺ B)
  mapM f = sequence ∘ map f

open Monadic public

------------------------------------------------------------------------
-- List⁺ monad transformer

monadT : ∀ {f M} → RawMonad {f} M → RawMonad (M ∘′ List⁺)
monadT M = record
  { return = pure ∘′ [_]
  ; _>>=_  = λ mas f → mas >>= λ as → concat <$> mapM M f as
  } where open RawMonad M
