------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of Maybe
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Maybe.Categorical where

open import Level
open import Data.Maybe.Base
open import Category.Functor
open import Category.Applicative
open import Category.Monad
import Function.Identity.Categorical as Id
open import Function

private
  variable
    a b f m : Level
    A : Set a
    B : Set b
    F : Set f → Set f
    M : Set m → Set m

------------------------------------------------------------------------
-- Maybe applicative functor

functor : RawFunctor {a} Maybe
functor = record
  { _<$>_ = map
  }

applicative : RawApplicative {a} Maybe
applicative = record
  { pure = just
  ; _⊛_  = maybe map (const nothing)
  }

applicativeZero : RawApplicativeZero {a} Maybe
applicativeZero = record
  { applicative = applicative
  ; ∅           = nothing
  }

alternative : RawAlternative {a} Maybe
alternative = record
  { applicativeZero = applicativeZero
  ; _∣_             = _<∣>_
  }

------------------------------------------------------------------------
-- Maybe monad transformer

monadT : RawMonadT {a} (_∘′ Maybe)
monadT M = record
  { return = M.return ∘ just
  ; _>>=_  = λ m f → m M.>>= maybe f (M.return nothing)
  }
  where module M = RawMonad M

------------------------------------------------------------------------
-- Maybe monad

monad : RawMonad {a} Maybe
monad = monadT Id.monad

monadZero : RawMonadZero {a} Maybe
monadZero = record
  { monad           = monad
  ; applicativeZero = applicativeZero
  }

monadPlus : RawMonadPlus {a} Maybe
monadPlus {a} = record
  { monad       = monad
  ; alternative = alternative
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA (App : RawApplicative F) where

  open RawApplicative App

  sequenceA : Maybe (F A) → F (Maybe A)
  sequenceA nothing  = pure nothing
  sequenceA (just x) = just <$> x

  mapA : (A → F B) → Maybe A → F (Maybe B)
  mapA f = sequenceA ∘ map f

  forA : Maybe A → (A → F B) → F (Maybe B)
  forA = flip mapA

module TraversableM (Mon : RawMonad M) where

  open RawMonad Mon

  open TraversableA rawIApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )
