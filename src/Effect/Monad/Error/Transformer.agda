------------------------------------------------------------------------
-- The Agda standard library
--
-- The error monad transformer
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level

module Effect.Monad.Error.Transformer {e} (E : Set e) (a : Level) where

open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base

private
  variable
    f ℓ : Level
    A B : Set ℓ
    M : Set f → Set f

------------------------------------------------------------------------
-- Error monad operations

record RawMonadError
       (M : Set (e ⊔ a) → Set (e ⊔ a))
       : Set (suc (e ⊔ a)) where
  field
    rawMonad : RawMonad M
    throw : E → M A
    catch : M A → (E → M A) → M A

  open RawMonad rawMonad public

  during : (E → E) → M A → M A
  during f ma = catch ma (throw ∘′ f)

------------------------------------------------------------------------
-- Monad error transformer specifics

module Sumₗ where

  open import Data.Sum using (inj₁; inj₂; [_,_]′)
  open import Data.Sum.Effectful.Left.Transformer E a

  monadError : RawMonad M → RawMonadError (SumₗT M)
  monadError M = record
    { rawMonad = monad M
    ; throw = mkSumₗT ∘′ pure ∘′ inj₁
    ; catch = λ ma k → mkSumₗT $ do
                         a ← runSumₗT ma
                         [ runSumₗT ∘′ k , pure ∘′ inj₂ ]′ a
    } where open RawMonad M

module Sumᵣ where

  open import Data.Sum using (inj₁; inj₂; [_,_]′)
  open import Data.Sum.Effectful.Right.Transformer a E

  monadError : RawMonad M → RawMonadError (SumᵣT M)
  monadError M = record
    { rawMonad = monad M
    ; throw = mkSumᵣT ∘′ pure ∘′ inj₂
    ; catch = λ ma k → mkSumᵣT $ do
                         a ← runSumᵣT ma
                         [ pure ∘′ inj₁ , runSumᵣT ∘′ k ]′ a
    } where open RawMonad M
