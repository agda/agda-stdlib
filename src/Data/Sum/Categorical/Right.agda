------------------------------------------------------------------------
-- The Agda standard library
--
-- A Categorical view of the Sum type (Right-biased)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level

module Data.Sum.Categorical.Right (a : Level) {b} (B : Set b) where

open import Data.Sum.Base
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Function
import Function.Identity.Categorical as Id

Sumᵣ : Set (a ⊔ b) → Set (a ⊔ b)
Sumᵣ A = A ⊎ B

functor : RawFunctor Sumᵣ
functor = record { _<$>_ = map₁ }

applicative : RawApplicative Sumᵣ
applicative = record
  { pure = inj₁
  ; _⊛_ = [ map₁ , const ∘ inj₂ ]′
  }

monadT : RawMonadT (_∘′ Sumᵣ)
monadT M = record
  { return = M.pure ∘′ inj₁
  ; _>>=_  = λ ma f → ma M.>>= [ f , M.pure ∘′ inj₂ ]′
  } where module M = RawMonad M

monad : RawMonad Sumᵣ
monad = monadT Id.monad

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {F} (App : RawApplicative {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Sumᵣ (F A) → F (Sumᵣ A)
  sequenceA (inj₂ a) = pure (inj₂ a)
  sequenceA (inj₁ x) = inj₁ <$> x

  mapA : ∀ {A B} → (A → F B) → Sumᵣ A → F (Sumᵣ B)
  mapA f = sequenceA ∘ map₁ f

  forA : ∀ {A B} → Sumᵣ A → (A → F B) → F (Sumᵣ B)
  forA = flip mapA

module TraversableM {M} (Mon : RawMonad {a ⊔ b} M) where

  open RawMonad Mon

  open TraversableA rawIApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )

