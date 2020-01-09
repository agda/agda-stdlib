------------------------------------------------------------------------
-- The Agda standard library
--
-- A Categorical view of the Sum type (Left-biased)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level

module Data.Sum.Categorical.Left {a} (A : Set a) (b : Level) where

open import Data.Sum
open import Category.Functor
open import Category.Applicative
open import Category.Monad
import Function.Identity.Categorical as Id
open import Function

-- To minimize the universe level of the RawFunctor, we require that elements of
-- B are "lifted" to a copy of B at a higher universe level (a ⊔ b). See the
-- examples for how this is done.

------------------------------------------------------------------------
-- Left-biased monad instance for _⊎_

Sumₗ : Set (a ⊔ b) → Set (a ⊔ b)
Sumₗ B = A ⊎ B

functor : RawFunctor Sumₗ
functor = record { _<$>_ = map₂ }

applicative : RawApplicative Sumₗ
applicative = record
  { pure = inj₂
  ; _⊛_ = [ const ∘ inj₁ , map₂ ]′
  }

-- The monad instance also requires some mucking about with universe levels.
monadT : RawMonadT (_∘′ Sumₗ)
monadT M = record
  { return = M.pure ∘ inj₂
  ; _>>=_  = λ ma f → ma M.>>= [ M.pure ∘′ inj₁ , f ]′
  } where module M = RawMonad M

monad : RawMonad Sumₗ
monad = monadT Id.monad

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {F} (App : RawApplicative {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Sumₗ (F A) → F (Sumₗ A)
  sequenceA (inj₁ a) = pure (inj₁ a)
  sequenceA (inj₂ x) = inj₂ <$> x

  mapA : ∀ {A B} → (A → F B) → Sumₗ A → F (Sumₗ B)
  mapA f = sequenceA ∘ map₂ f

  forA : ∀ {A B} → Sumₗ A → (A → F B) → F (Sumₗ B)
  forA = flip mapA

module TraversableM {M} (Mon : RawMonad {a ⊔ b} M) where

  open RawMonad Mon

  open TraversableA rawIApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )

