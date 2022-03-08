------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of Maybe
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Maybe.Effectful where

open import Level
open import Data.Maybe.Base
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
import Function.Identity.Effectful as Id
open import Function

private
  variable
    a b f m : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Maybe applicative functor

functor : RawFunctor {f} Maybe
functor = record
  { _<$>_ = map
  }

applicative : RawApplicative {f} Maybe
applicative = record
  { pure = just
  ; _⊛_  = maybe map (const nothing)
  }

applicativeZero : RawApplicativeZero {f} Maybe
applicativeZero = record
  { applicative = applicative
  ; ∅           = nothing
  }

alternative : RawAlternative {f} Maybe
alternative = record
  { applicativeZero = applicativeZero
  ; _∣_             = _<∣>_
  }

------------------------------------------------------------------------
-- Maybe monad transformer

monadT : RawMonadT {f} (_∘′ Maybe)
monadT M = record
  { return = M.return ∘ just
  ; _>>=_  = λ m f → m M.>>= maybe f (M.return nothing)
  }
  where module M = RawMonad M

------------------------------------------------------------------------
-- Maybe monad

monad : RawMonad {f} Maybe
monad = monadT Id.monad

monadZero : RawMonadZero {f} Maybe
monadZero = record
  { monad           = monad
  ; applicativeZero = applicativeZero
  }

monadPlus : RawMonadPlus {f} Maybe
monadPlus {f} = record
  { monad       = monad
  ; alternative = alternative
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {F} (App : RawApplicative {f} F) where

  open RawApplicative App

  sequenceA : Maybe (F A) → F (Maybe A)
  sequenceA nothing  = pure nothing
  sequenceA (just x) = just <$> x

  mapA : (A → F B) → Maybe A → F (Maybe B)
  mapA f = sequenceA ∘ map f

  forA : Maybe A → (A → F B) → F (Maybe B)
  forA = flip mapA

module TraversableM {M} (Mon : RawMonad {m} M) where

  open RawMonad Mon

  open TraversableA rawIApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )
