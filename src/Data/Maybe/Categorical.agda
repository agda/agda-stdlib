------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of Maybe
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Maybe.Categorical where

open import Data.Maybe.Base
open import Category.Functor
open import Category.Applicative
open import Category.Monad
import Function.Identity.Categorical as Id
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

applicativeZero : ∀ {f} → RawApplicativeZero {f} Maybe
applicativeZero = record
  { applicative = applicative
  ; ∅           = nothing
  }

alternative : ∀ {f} → RawAlternative {f} Maybe
alternative = record
  { applicativeZero = applicativeZero
  ; _∣_             = _<∣>_
  }

------------------------------------------------------------------------
-- Maybe monad transformer

monadT : ∀ {f} → RawMonadT {f} (_∘′ Maybe)
monadT M = record
  { return = M.return ∘ just
  ; _>>=_  = λ m f → m M.>>= maybe f (M.return nothing)
  }
  where module M = RawMonad M

------------------------------------------------------------------------
-- Maybe monad

monad : ∀ {f} → RawMonad {f} Maybe
monad = monadT Id.monad

monadZero : ∀ {f} → RawMonadZero {f} Maybe
monadZero = record
  { monad           = monad
  ; applicativeZero = applicativeZero
  }

monadPlus : ∀ {f} → RawMonadPlus {f} Maybe
monadPlus {f} = record
  { monad       = monad
  ; alternative = alternative
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {f F} (App : RawApplicative {f} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Maybe (F A) → F (Maybe A)
  sequenceA nothing  = pure nothing
  sequenceA (just x) = just <$> x

  mapA : ∀ {a} {A : Set a} {B} → (A → F B) → Maybe A → F (Maybe B)
  mapA f = sequenceA ∘ map f

  forA : ∀ {a} {A : Set a} {B} → Maybe A → (A → F B) → F (Maybe B)
  forA = flip mapA

module TraversableM {m M} (Mon : RawMonad {m} M) where

  open RawMonad Mon

  open TraversableA rawIApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )
