------------------------------------------------------------------------
-- The Agda standard library
--
-- Base definitions for the right-biased universe-sensitive functor and
-- monad instances for These.
--
-- To minimize the universe level of the RawFunctor, we require that
-- elements of B are "lifted" to a copy of B at a higher universe level
-- (a ⊔ b).
-- See the Data.Product.Effectful.Examples for how this is done in a
-- Product-based similar setting.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level

module Data.These.Effectful.Right.Base (a : Level) {b} (B : Set b) where

open import Data.These.Base
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base using (flip; _∘_)

Theseᵣ : Set (a ⊔ b) → Set (a ⊔ b)
Theseᵣ A = These A B

functor : RawFunctor Theseᵣ
functor = record { _<$>_ = map₁ }

------------------------------------------------------------------------
-- Get access to other monadic functions

module _ {F} (App : RawApplicative {a ⊔ b} {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Theseᵣ (F A) → F (Theseᵣ A)
  sequenceA (this a)    = this <$> a
  sequenceA (that b)    = pure (that b)
  sequenceA (these a b) = flip these b <$> a

  mapA : ∀ {A B} → (A → F B) → Theseᵣ A → F (Theseᵣ B)
  mapA f = sequenceA ∘ map₁ f

  forA : ∀ {A B} → Theseᵣ A → (A → F B) → F (Theseᵣ B)
  forA = flip mapA

module _ {M} (Mon : RawMonad {a ⊔ b} {a ⊔ b} M) where

  private App = RawMonad.rawApplicative Mon

  sequenceM : ∀ {A} → Theseᵣ (M A) → M (Theseᵣ A)
  sequenceM = sequenceA App

  mapM : ∀ {A B} → (A → M B) → Theseᵣ A → M (Theseᵣ B)
  mapM = mapA App

  forM : ∀ {A B} → Theseᵣ A → (A → M B) → M (Theseᵣ B)
  forM = forA App
