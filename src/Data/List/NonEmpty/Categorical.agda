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

module _ {f F} (App : RawApplicative {f} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → List⁺ (F A) → F (List⁺ A)
  sequenceA (x ∷ xs) = _∷_ <$> x ⊛ List.sequenceA App xs

  mapA : ∀ {a} {A : Set a} {B} → (A → F B) → List⁺ A → F (List⁺ B)
  mapA f = sequenceA ∘ map f

  forA : ∀ {a} {A : Set a} {B} → List⁺ A → (A → F B) → F (List⁺ B)
  forA = flip mapA

module _ {m M} (Mon : RawMonad {m} M) where

  private App = RawMonad.rawIApplicative Mon

  sequenceM = sequenceA App
  mapM = mapA App
  forM = forA App

------------------------------------------------------------------------
-- List⁺ monad transformer

monadT : ∀ {f M} → RawMonad {f} M → RawMonad (M ∘′ List⁺)
monadT M = record
  { return = pure ∘′ [_]
  ; _>>=_  = λ mas f → mas >>= λ as → concat <$> mapM M f as
  } where open RawMonad M
