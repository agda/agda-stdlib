------------------------------------------------------------------------
-- The Agda standard library
--
-- Right-biased universe-sensitive functor and monad instances for the
-- Product type.
--
-- To minimize the universe level of the RawFunctor, we require that
-- elements of B are "lifted" to a copy of B at a higher universe level
-- (a ⊔ b). See the Data.Product.Categorical.Examples for how this is
-- done.
------------------------------------------------------------------------

open import Algebra
open import Level

module Data.Product.Categorical.Right
  (a : Level) {b e} (B : RawMonoid b e) where

open import Data.Product
import Data.Product.Categorical.Right.Base as Base
open import Category.Applicative using (RawApplicative)
open import Category.Monad using (RawMonad; RawMonadT)
open import Function using (id; flip; _∘_; _∘′_)
import Function.Identity.Categorical as Id

open RawMonoid B

------------------------------------------------------------------------
-- Re-export the base contents publically

open Base Carrier a public

------------------------------------------------------------------------
-- Basic records

applicative : RawApplicative Productᵣ
applicative = record
  { pure = _, ε
  ; _⊛_  = zip id _∙_
  }

monadT : RawMonadT (_∘′ Productᵣ)
monadT M = record
  { return = pure ∘′ (_, ε)
  ; _>>=_  = λ ma f → ma >>= uncurry λ x b → map₂ (b ∙_) <$> f x
  } where open RawMonad M

monad : RawMonad Productᵣ
monad = monadT Id.monad

------------------------------------------------------------------------
-- Get access to other monadic functions

module _ {F} (App : RawApplicative {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Productᵣ (F A) → F (Productᵣ A)
  sequenceA (fa , y) = (_, y) <$> fa

  mapA : ∀ {A B} → (A → F B) → Productᵣ A → F (Productᵣ B)
  mapA f = sequenceA ∘ map₁ f

  forA : ∀ {A B} → Productᵣ A → (A → F B) → F (Productᵣ B)
  forA = flip mapA

module _ {M} (Mon : RawMonad {a ⊔ b} M) where

  private App = RawMonad.rawIApplicative Mon

  sequenceM : ∀ {A} → Productᵣ (M A) → M (Productᵣ A)
  sequenceM = sequenceA App

  mapM : ∀ {A B} → (A → M B) → Productᵣ A → M (Productᵣ B)
  mapM = mapA App

  forM : ∀ {A B} → Productᵣ A → (A → M B) → M (Productᵣ B)
  forM = forA App
