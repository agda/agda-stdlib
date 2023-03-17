------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of vectors defined by recursion
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Recursive.Effectful where

open import Agda.Builtin.Nat
open import Data.Product hiding (map)
open import Data.Vec.Recursive
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function

------------------------------------------------------------------------
-- Functor and applicative

functor : ∀ {ℓ} n → RawFunctor {ℓ} (_^ n)
functor n = record { _<$>_ = λ f → map f n }

applicative : ∀ {ℓ} n → RawApplicative {ℓ} (_^ n)
applicative n = record
  { rawFunctor = functor n
  ; pure = replicate n
  ; _<*>_  = ap n
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

module _ {f g F} (App : RawApplicative {f} {g} F) where

  open RawApplicative App

  sequenceA : ∀ {n A} → F A ^ n → F (A ^ n)
  sequenceA {0}    _                 = pure _
  sequenceA {1}    fa                = fa
  sequenceA {suc (suc _)} (fa , fas) = _,_ <$> fa ⊛ sequenceA fas

  mapA : ∀ {n a} {A : Set a} {B} → (A → F B) → A ^ n → F (B ^ n)
  mapA f = sequenceA ∘ map f _

  forA : ∀ {n a} {A : Set a} {B} → A ^ n → (A → F B) → F (B ^ n)
  forA = flip mapA

module _ {m n M} (Mon : RawMonad {m} {n} M) where

  private App = RawMonad.rawApplicative Mon

  sequenceM : ∀ {n A} → M A ^ n → M (A ^ n)
  sequenceM = sequenceA App

  mapM : ∀ {n a} {A : Set a} {B} → (A → M B) → A ^ n → M (B ^ n)
  mapM = mapA App

  forM : ∀ {n a} {A : Set a} {B} → A ^ n → (A → M B) → M (B ^ n)
  forM = forA App
