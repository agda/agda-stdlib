------------------------------------------------------------------------
-- The Agda standard library
--
-- Base definitions for the left-biased universe-sensitive functor and
-- monad instances for These.
--
-- To minimize the universe level of the RawFunctor, we require that
-- elements of B are "lifted" to a copy of B at a higher universe level
-- (a ⊔ b).
-- See the Data.Product.Categorical.Examples for how this is done in a
-- Product-based similar setting.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Level

module Data.These.Categorical.Left.Base {a} (A : Set a) (b : Level) where

open import Data.These
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Function

Theseₗ : Set (a ⊔ b) → Set (a ⊔ b)
Theseₗ B = These A B

functor : RawFunctor Theseₗ
functor = record { _<$>_ = map₂ }

------------------------------------------------------------------------
-- Get access to other monadic functions

module _ {F} (App : RawApplicative {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Theseₗ (F A) → F (Theseₗ A)
  sequenceA (this a)    = pure (this a)
  sequenceA (that b)    = that <$> b
  sequenceA (these a b) = these a <$> b

  mapA : ∀ {A B} → (A → F B) → Theseₗ A → F (Theseₗ B)
  mapA f = sequenceA ∘ map₂ f

  forA : ∀ {A B} → Theseₗ A → (A → F B) → F (Theseₗ B)
  forA = flip mapA

module _ {M} (Mon : RawMonad {a ⊔ b} M) where

  private App = RawMonad.rawIApplicative Mon

  sequenceM : ∀ {A} → Theseₗ (M A) → M (Theseₗ A)
  sequenceM = sequenceA App

  mapM : ∀ {A B} → (A → M B) → Theseₗ A → M (Theseₗ B)
  mapM = mapA App

  forM : ∀ {A B} → Theseₗ A → (A → M B) → M (Theseₗ B)
  forM = forA App
