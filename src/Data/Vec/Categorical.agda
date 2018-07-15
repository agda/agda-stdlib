------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of Vec
------------------------------------------------------------------------

module Data.Vec.Categorical {a n} where

open import Category.Applicative using (RawApplicative)
open import Category.Applicative.Indexed using (Morphism)
open import Category.Functor as Fun using (RawFunctor)
open import Category.Functor.Identity using (IdentityFunctor)
open import Category.Monad using (RawMonad)
open import Category.Monad.Identity using (IdentityMonad)
open import Data.Fin using (Fin)
open import Data.Vec as Vec hiding (_⊛_)
open import Data.Vec.Properties
open import Function

functor : RawFunctor (λ (A : Set a) → Vec A n)
functor = record
  { _<$>_ = map
  }

applicative : RawApplicative (λ (A : Set a) → Vec A n)
applicative = record
  { pure = replicate
  ; _⊛_  = Vec._⊛_
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

module _ {f F} (App : RawApplicative {f} F) where

  open RawApplicative App

  sequenceA : ∀ {A n} → Vec (F A) n → F (Vec A n)
  sequenceA []       = pure []
  sequenceA (x ∷ xs) = _∷_ <$> x ⊛ sequenceA xs

  mapA : ∀ {a} {A : Set a} {B n} → (A → F B) → Vec A n → F (Vec B n)
  mapA f = sequenceA ∘ map f

  forA : ∀ {a} {A : Set a} {B n} → Vec A n → (A → F B) → F (Vec B n)
  forA = flip mapA

module _ {m M} (Mon : RawMonad {m} M) where

  private App = RawMonad.rawIApplicative Mon

  sequenceM = sequenceA App
  mapM = mapA App
  forM = forA App

-- lookup is a functor morphism from Vec to Identity.

lookup-functor-morphism : (i : Fin n) →
                          Fun.Morphism functor IdentityFunctor
lookup-functor-morphism i = record
  { op     = lookup i
  ; op-<$> = lookup-map i
  }

-- lookup is an applicative functor morphism.

lookup-morphism : (i : Fin n) →
                  Morphism applicative (RawMonad.rawIApplicative IdentityMonad)
lookup-morphism i = record
  { op      = lookup i
  ; op-pure = lookup-replicate i
  ; op-⊛    = lookup-⊛ i
  }
