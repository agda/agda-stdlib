------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of Maybe
------------------------------------------------------------------------

module Data.Maybe.Categorical where

open import Data.Maybe.Base
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Category.Monad.Identity
open import Function

------------------------------------------------------------------------
-- Maybe applicative functor

functor : ∀ {f} → RawFunctor {f} Maybe
functor = record
  { _<$>_ = map
  }

applicative : ∀ {f} → RawApplicative {f} Maybe
applicative = record
  { pure = just
  ; _⊛_  = maybe map (const nothing)
  }

------------------------------------------------------------------------
-- Maybe monad transformer

monadT : ∀ {f M} → RawMonad {f} M → RawMonad (M ∘′ Maybe)
monadT M = record
  { return = M.return ∘ just
  ; _>>=_  = λ m f → m M.>>= maybe f (M.return nothing)
  }
  where module M = RawMonad M

------------------------------------------------------------------------
-- Maybe monad

monad : ∀ {f} → RawMonad {f} Maybe
monad = monadT IdentityMonad

monadZero : ∀ {f} → RawMonadZero {f} Maybe
monadZero = record
  { monad = monad
  ; ∅     = nothing
  }

monadPlus : ∀ {f} → RawMonadPlus {f} Maybe
monadPlus {f} = record
  { monadZero = monadZero
  ; _∣_       = maybe′ (const ∘ just) id
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

module _ {f F} (App : RawApplicative {f} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Maybe (F A) → F (Maybe A)
  sequenceA nothing  = pure nothing
  sequenceA (just x) = just <$> x

  mapA : ∀ {a} {A : Set a} {B} → (A → F B) → Maybe A → F (Maybe B)
  mapA f = sequenceA ∘ map f

  forA : ∀ {a} {A : Set a} {B} → Maybe A → (A → F B) → F (Maybe B)
  forA = flip mapA

module _ {m M} (Mon : RawMonad {m} M) where

  private App = RawMonad.rawIApplicative Mon

  sequenceM = sequenceA App
  mapM = mapA App
  forM = forA App
