------------------------------------------------------------------------
-- The Agda standard library
--
-- Left-biased universe-sensitive functor and monad instances for the
-- Product type.
--
-- To minimize the universe level of the RawFunctor, we require that
-- elements of B are "lifted" to a copy of B at a higher universe level
-- (a ⊔ b). See the Data.Product.Categorical.Examples for how this is
-- done.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Level

module Data.Product.Categorical.Left
  {a e} (A : RawMonoid a e) (b : Level) where

open import Data.Product
import Data.Product.Categorical.Left.Base as Base
open import Category.Applicative using (RawApplicative)
open import Category.Monad using (RawMonad; RawMonadT)
open import Function using (id; flip; _∘_; _∘′_)
import Function.Identity.Categorical as Id

open RawMonoid A

------------------------------------------------------------------------
-- Re-export the base contents publically

open Base Carrier b public

------------------------------------------------------------------------
-- Basic records

applicative : RawApplicative Productₗ
applicative = record
  { pure = ε ,_
  ; _⊛_  = zip _∙_ id
  }

-- The monad instance also requires some mucking about with universe levels.
monadT : RawMonadT (_∘′ Productₗ)
monadT M = record
  { return = pure ∘′ (ε ,_)
  ; _>>=_  = λ ma f → ma >>= uncurry λ a x → map₁ (a ∙_) <$> f x
  } where open RawMonad M

monad : RawMonad Productₗ
monad = monadT Id.monad

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {F} (App : RawApplicative {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Productₗ (F A) → F (Productₗ A)
  sequenceA (x , fa) = (x ,_) <$> fa

  mapA : ∀ {A B} → (A → F B) → Productₗ A → F (Productₗ B)
  mapA f = sequenceA ∘ map₂ f

  forA : ∀ {A B} → Productₗ A → (A → F B) → F (Productₗ B)
  forA = flip mapA

module TraversableM {M} (Mon : RawMonad {a ⊔ b} M) where

  open RawMonad Mon

  open TraversableA rawIApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )
