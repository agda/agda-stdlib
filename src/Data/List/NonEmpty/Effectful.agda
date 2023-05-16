------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of List⁺
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.NonEmpty.Effectful where

open import Agda.Builtin.List
import Data.List.Effectful as List
open import Data.List.NonEmpty.Base
open import Data.Product using (uncurry)
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Effect.Comonad
open import Function

------------------------------------------------------------------------
-- List⁺ applicative functor

functor : ∀ {f} → RawFunctor {f} List⁺
functor = record
  { _<$>_ = map
  }

applicative : ∀ {f} → RawApplicative {f} List⁺
applicative = record
  { rawFunctor = functor
  ; pure = [_]
  ; _<*>_  = ap
  }

------------------------------------------------------------------------
-- List⁺ monad

monad : ∀ {f} → RawMonad {f} List⁺
monad = record
  { rawApplicative = applicative
  ; _>>=_  = flip concatMap
  }

------------------------------------------------------------------------
-- List⁺ comonad

comonad : ∀ {f} → RawComonad {f} List⁺
comonad = record
  { extract = head
  ; extend  = λ f → uncurry (extend f) ∘′ uncons
  } where

  extend : ∀ {A B} → (List⁺ A → B) → A → List A → List⁺ B
  extend f x xs@[]       = f (x ∷ xs) ∷ []
  extend f x xs@(y ∷ ys) = f (x ∷ xs) ∷⁺ extend f y ys


------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {f g F} (App : RawApplicative {f} {g} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → List⁺ (F A) → F (List⁺ A)
  sequenceA (x ∷ xs) = _∷_ <$> x ⊛ List.TraversableA.sequenceA App xs

  mapA : ∀ {a} {A : Set a} {B} → (A → F B) → List⁺ A → F (List⁺ B)
  mapA f = sequenceA ∘ map f

  forA : ∀ {a} {A : Set a} {B} → List⁺ A → (A → F B) → F (List⁺ B)
  forA = flip mapA

module TraversableM {m n M} (Mon : RawMonad {m} {n} M) where

  open RawMonad Mon

  open TraversableA rawApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )
