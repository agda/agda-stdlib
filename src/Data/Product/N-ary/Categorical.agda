------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of N-ary products
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Product.N-ary.Categorical where

open import Agda.Builtin.Nat
open import Data.Product hiding (map)
open import Data.Product.N-ary
open import Function

open import Category.Functor
open import Category.Applicative
open import Category.Monad

------------------------------------------------------------------------
-- Functor and applicative

functor : ∀ {ℓ} n → RawFunctor {ℓ} (_^ n)
functor n = record { _<$>_ = λ f → map f n }

applicative : ∀ {ℓ} n → RawApplicative {ℓ} (_^ n)
applicative n = record
  { pure = replicate n
  ; _⊛_  = ap n
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

module _ {f F} (App : RawApplicative {f} F) where

  open RawApplicative App

  sequenceA : ∀ {n A} → F A ^ n → F (A ^ n)
  sequenceA {0}    _          = pure _
  sequenceA {1}    fa         = fa
  sequenceA {2+ n} (fa , fas) = _,_ <$> fa ⊛ sequenceA fas

  mapA : ∀ {n a} {A : Set a} {B} → (A → F B) → A ^ n → F (B ^ n)
  mapA f = sequenceA ∘ map f _

  forA : ∀ {n a} {A : Set a} {B} → A ^ n → (A → F B) → F (B ^ n)
  forA = flip mapA

module _ {m M} (Mon : RawMonad {m} M) where

  private App = RawMonad.rawIApplicative Mon

  sequenceM : ∀ {n A} → M A ^ n → M (A ^ n)
  sequenceM = sequenceA App

  mapM : ∀ {n a} {A : Set a} {B} → (A → M B) → A ^ n → M (B ^ n)
  mapM = mapA App

  forM : ∀ {n a} {A : Set a} {B} → A ^ n → (A → M B) → M (B ^ n)
  forM = forA App
