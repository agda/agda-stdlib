------------------------------------------------------------------------
-- The Agda standard library
--
-- Base definitions for the right-biased universe-sensitive functor and
-- monad instances for These.
--
-- To minimize the universe level of the RawFunctor, we require that
-- elements of B are "lifted" to a copy of B at a higher universe level
-- (a ⊔ b).
-- See the Data.Product.Categorical.Examples for how this is done in a
-- Product-based similar setting.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level

module Data.These.Categorical.Right.Base (a : Level) {b} (B : Set b) where

open import Data.These
open import Category.Construct.Agda.Functor
open import Category.Applicative
open import Category.Monad
open import Function

Theseᵣ : Set (a ⊔ b) → Set (a ⊔ b)
Theseᵣ A = These A B

functor : RawFunctor Theseᵣ
functor = record { _<$>_ = map₁ }

------------------------------------------------------------------------
-- Get access to other monadic functions

module _ {F} (App : RawApplicative {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Theseᵣ (F A) → F (Theseᵣ A)
  sequenceA (this a)    = this <$> a
  sequenceA (that b)    = pure (that b)
  sequenceA (these a b) = flip these b <$> a

  mapA : ∀ {A B} → (A → F B) → Theseᵣ A → F (Theseᵣ B)
  mapA f = sequenceA ∘ map₁ f

  forA : ∀ {A B} → Theseᵣ A → (A → F B) → F (Theseᵣ B)
  forA = flip mapA

module _ {M} (Mon : RawMonad {a ⊔ b} M) where

  private App = RawMonad.rawIApplicative Mon

  sequenceM : ∀ {A} → Theseᵣ (M A) → M (Theseᵣ A)
  sequenceM = sequenceA App

  mapM : ∀ {A B} → (A → M B) → Theseᵣ A → M (Theseᵣ B)
  mapM = mapA App

  forM : ∀ {A B} → Theseᵣ A → (A → M B) → M (Theseᵣ B)
  forM = forA App
