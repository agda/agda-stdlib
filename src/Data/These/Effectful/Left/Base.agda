------------------------------------------------------------------------
-- The Agda standard library
--
-- Base definitions for the left-biased universe-sensitive functor and
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

module Data.These.Effectful.Left.Base {a} (A : Set a) (b : Level) where

open import Data.These.Base using (These; this; that; these; map₂)
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)
open import Function.Base using (_∘_; flip)

Theseₗ : Set (a ⊔ b) → Set (a ⊔ b)
Theseₗ B = These A B

functor : RawFunctor Theseₗ
functor = record { _<$>_ = map₂ }

------------------------------------------------------------------------
-- Get access to other monadic functions

module _ {F} (App : RawApplicative {a ⊔ b} {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Theseₗ (F A) → F (Theseₗ A)
  sequenceA (this a)    = pure (this a)
  sequenceA (that b)    = that <$> b
  sequenceA (these a b) = these a <$> b

  mapA : ∀ {A B} → (A → F B) → Theseₗ A → F (Theseₗ B)
  mapA f = sequenceA ∘ map₂ f

  forA : ∀ {A B} → Theseₗ A → (A → F B) → F (Theseₗ B)
  forA = flip mapA

module _ {M} (Mon : RawMonad {a ⊔ b} {a ⊔ b} M) where

  private App = RawMonad.rawApplicative Mon

  sequenceM : ∀ {A} → Theseₗ (M A) → M (Theseₗ A)
  sequenceM = sequenceA App

  mapM : ∀ {A B} → (A → M B) → Theseₗ A → M (Theseₗ B)
  mapM = mapA App

  forM : ∀ {A B} → Theseₗ A → (A → M B) → M (Theseₗ B)
  forM = forA App
