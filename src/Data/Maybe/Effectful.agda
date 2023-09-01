------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of Maybe
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Maybe.Effectful where

open import Level
open import Data.Maybe.Base

open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad

open import Function.Base

private
  variable
    a b f g m n : Level
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
  { rawFunctor = functor
  ; pure       = just
  ; _<*>_      = maybe map (const nothing)
  }

empty : RawEmpty {f} Maybe
empty = record { empty = nothing }

choice : RawChoice {f} Maybe
choice = record { _<|>_ = _<∣>_ }

applicativeZero : RawApplicativeZero {f} Maybe
applicativeZero = record
  { rawApplicative = applicative
  ; rawEmpty       = empty
  }

alternative : RawAlternative {f} Maybe
alternative = record
  { rawApplicativeZero = applicativeZero
  ; rawChoice          = choice
  }

------------------------------------------------------------------------
-- Maybe monad

monad : RawMonad {f} Maybe
monad = record
  { rawApplicative = applicative
  ; _>>=_ = _>>=_
  }

monadZero : RawMonadZero {f} Maybe
monadZero = record
  { rawMonad = monad
  ; rawEmpty = empty
  }

monadPlus : RawMonadPlus {f} Maybe
monadPlus {f} = record
  { rawMonadZero = monadZero
  ; rawChoice    = choice
  }

module TraversableA {F} (App : RawApplicative {f} {g} F) where

  open RawApplicative App

  sequenceA : Maybe (F A) → F (Maybe A)
  sequenceA nothing  = pure nothing
  sequenceA (just x) = just <$> x

  mapA : (A → F B) → Maybe A → F (Maybe B)
  mapA f = sequenceA ∘ map f

  forA : Maybe A → (A → F B) → F (Maybe B)
  forA = flip mapA

module TraversableM {M} (Mon : RawMonad {m} {n} M) where

  open RawMonad Mon

  open TraversableA rawApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )
